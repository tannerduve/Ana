"""Independent audit fixtures reject altered framing, counters, events and bytes."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "runner"))
from audit_continuation import AuditError, compact, repair_message
from session_audit import completed_session
from request_evidence import outbound_evidence
from continuation_audit import recorded_schema7


class SessionAudit(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.session = self.directory / "sessions/session"
        self.session.mkdir(parents=True)
        config = {"maxModelAttempts": 2, "maxToolCalls": 2,
                  "maxArtifactBytes": 1024, "maxSessionArtifactBytes": 2048}
        self.state = {"schemaVersion": 3, "config": config, "sessionId": "fixture",
                      "phase": {"stopped": {"outcome": {"final": {"answer": "done"}}}},
                      "nextId": 1, "modelAttempts": 1, "toolDispatches": 0,
                      "seenCallIds": [], "artifacts": [], "knownInputTokens": 7,
                      "knownOutputTokens": 3, "unknownUsage": 0}
        self.inspection = {"state": self.state, "terminal": True, "pending": False,
                           "interruptedStorage": False}
        self.records = [{"kind": "initial", "schema": 3, "session": "fixture", "config": config},
                        {"kind": "intent", "id": 0, "action": {"kind": "model"}},
                        {"kind": "completion", "id": 0, "observation": {
                            "success": {"response": {"usage": {"inputTokens": 7, "outputTokens": 3}}}}},
                        {"kind": "terminal", "id": 1, "outcome": self.state["phase"]["stopped"]["outcome"]}]
        self.charges = [{"active": False, "attempt": 1,
                         "usage": {"input_tokens": 7, "output_tokens": 3}}]
        self.write_frames()
        self.events = [{"event": "finished", "operation": 1, "data": self.records[-1]["outcome"],
                        "outputLossIncidents": 0}]
        self.write_events()

    def write_frames(self):
        previous, frames = "", []
        for seq, record in enumerate(self.records):
            frame = {"v": 1, "seq": seq, "previous": previous, "record": record}
            previous = hashlib.sha256(compact(frame).encode()).hexdigest()
            frames.append({**frame, "checksum": previous})
        (self.session / "journal.jsonl").write_text("".join(compact(frame)+"\n" for frame in frames))

    def write_events(self):
        (self.directory / "events.log").write_text("".join(compact(event)+"\n" for event in self.events))

    def audit(self):
        return completed_session(self.directory, self.inspection, copy.deepcopy(self.inspection),
                                 self.charges, normal=True)

    def test_valid_fixture_and_independent_counter_check(self):
        report = self.audit()
        self.assertTrue(report["passed"])
        self.assertEqual(report["request_evidence"]["status"], "unavailable_legacy")
        self.state["modelAttempts"] = 0
        with self.assertRaisesRegex(AuditError, "reservation"):
            self.audit()

    def test_outbound_context_is_required_for_new_runs_and_checked_against_journal(self):
        request = {"system": "fixed instructions", "messages": [{"role": "user", "content": "task"}]}
        raw = json.dumps(request).encode()
        self.records[1]["action"]["request"] = copy.deepcopy(request)
        self.charges[0].update(outbound_evidence(raw)[1], request_bytes=len(raw))
        self.write_frames()
        def check():
            return completed_session(self.directory, self.inspection, copy.deepcopy(self.inspection),
                                     self.charges, normal=True, request_evidence_version=1)
        self.assertEqual(check()["request_evidence"]["matched_contexts"], 1)
        self.records[1]["action"]["request"]["system"] = "changed instruction"
        self.write_frames()
        with self.assertRaisesRegex(AuditError, "system/messages differ"): check()
        self.records[1]["action"]["request"] = request
        self.write_frames()
        del self.charges[0]["request_evidence_version"]
        with self.assertRaisesRegex(AuditError, "missing or unsupported"): check()

    def test_schema4_repair_counter_and_initial_schema_are_checked(self):
        self.state.update(schemaVersion=4, responseRepairs=1,
                          history=[{"role": "user", "content": []}, repair_message("invalidBatch")])
        self.state["config"]["maxResponseRepairs"] = 2
        self.records[0]["schema"] = 4
        self.write_frames()
        self.assertEqual(self.audit()["response_repairs"], 1)
        self.state["responseRepairs"] = 0
        with self.assertRaisesRegex(AuditError, "accepted feedback"):
            self.audit()
        self.state["responseRepairs"] = 1
        self.state["config"]["maxResponseRepairs"] = 0
        self.write_frames()
        with self.assertRaisesRegex(AuditError, "allowance"):
            self.audit()
        self.state["config"]["maxResponseRepairs"] = 2
        self.records[0]["schema"] = 3
        self.write_frames()
        with self.assertRaisesRegex(AuditError, "initial schema"):
            self.audit()

    def test_schema5_is_explicit_and_future_schema_is_not_inferred(self):
        self.state.update(schemaVersion=5, responseRepairs=0, history=[{"role": "user", "content": []}])
        self.state["config"]["maxResponseRepairs"] = 2
        self.records[0]["schema"] = 5
        self.write_frames()
        self.assertTrue(self.audit()["passed"])
        self.records[0]["schema"] = 4
        self.write_frames()
        with self.assertRaisesRegex(AuditError, "initial schema"):
            self.audit()
        self.state["schemaVersion"] = self.records[0]["schema"] = 6
        self.write_frames()
        with self.assertRaisesRegex(AuditError, "incompatible"):
            self.audit()

    def test_recorded_schema7_keeps_cumulative_counts_across_normal_and_cancelled_turns(self):
        for name, expected in [("schema7-coding", (11, 3)), ("schema7-cancelled", (3, 0))]:
            with self.subTest(name=name):
                run, broker, plan, _ = recorded_schema7(self.directory / name, name)
                inspected = json.loads((run / "inspection.json").read_text())
                replayed = json.loads((run / "replay.json").read_text())
                def audit(value=inspected, frozen=plan):
                    return completed_session(run, value, copy.deepcopy(value), broker["records"], normal=True, plan=frozen)
                report = completed_session(run, inspected, replayed, broker["records"], normal=True, plan=plan)
                self.assertEqual((report["model_attempts"], report["tool_dispatches"]), expected)
                self.assertEqual((report["user_turns"], report["declared_followups"]), (3, 2))
                with self.assertRaisesRegex(AuditError, "undeclared"):
                    audit(frozen={**plan, "user_turns": []})
                for field in ["modelAttempts", "toolDispatches", "knownOutputTokens", "nextId", "turn"]:
                    altered = copy.deepcopy(inspected)
                    altered["state"][field] += 1
                    with self.subTest(field=field), self.assertRaises(AuditError): audit(altered)
                altered = copy.deepcopy(inspected)
                altered["application"] = "inventory"
                with self.assertRaisesRegex(AuditError, "application identity"): audit(altered)
                events_path = run / "events.log"
                events = [json.loads(line) for line in events_path.read_text().splitlines()]
                next(event for event in events if event["event"] == "user_turn")["turn"] = 0
                events_path.write_text("".join(json.dumps(event) + "\n" for event in events))
                with self.assertRaisesRegex(AuditError, "user-turn event"): audit()

    def test_known_and_unknown_core_ledgers_are_checked_independently(self):
        for field in ("knownInputTokens", "knownOutputTokens", "unknownUsage"):
            previous = self.state[field]
            self.state[field] += 1
            with self.assertRaisesRegex(AuditError, "token ledger"):
                self.audit()
            self.state[field] = previous
        self.charges[0]["usage"]["input_tokens"] = 8
        with self.assertRaisesRegex(AuditError, "corresponding"):
            self.audit()

    def test_missing_provider_usage_remains_unknown_billing(self):
        self.charges[0]["usage"] = None
        usage = self.audit()["usage"]
        self.assertEqual(usage["provider_unknown_attempts"], 1)
        self.assertEqual(usage["core_unknown_attempts"], 0)
        self.assertEqual(usage["known_core_unknown_provider"], 1)
        self.assertEqual(usage["known_input_tokens"], 7)

    def test_each_unknown_core_observation_is_counted(self):
        observations = [{"success": {"response": {"usage": None}}},
                        {"failure": {"kind": "malformed", "message": "fixture"}},
                        "interrupted", {"uncertain": {"message": "lost"}}]
        for observation in observations:
            with self.subTest(observation=observation):
                self.records[2]["observation"] = observation
                self.state.update(knownInputTokens=0, knownOutputTokens=0, unknownUsage=1)
                self.write_frames()
                usage = self.audit()["usage"]
                self.assertEqual(usage["core_unknown_attempts"], 1)
                self.assertEqual(usage["unknown_core_known_provider"], 1)
                self.state["unknownUsage"] = 0
                with self.assertRaisesRegex(AuditError, "unknown token ledger"):
                    self.audit()

    def test_invalid_or_reordered_provider_counts_are_rejected(self):
        for attempt in [2, True]:
            self.charges[0]["attempt"] = attempt
            with self.assertRaisesRegex(AuditError, "reordered"):
                self.audit()
        self.charges[0]["attempt"] = 1
        self.charges[0]["usage"]["output_tokens"] = True
        with self.assertRaisesRegex(AuditError, "nonnegative"):
            self.audit()

    def test_unforwarded_reserved_attempt_does_not_invent_alignment(self):
        self.records[2]["observation"] = {"failure": {"kind": "transport", "message": "preflight"}}
        self.state.update(knownInputTokens=0, knownOutputTokens=0, unknownUsage=1)
        self.write_frames()
        result = completed_session(self.directory, self.inspection, copy.deepcopy(self.inspection), [], normal=False)
        self.assertFalse(result["usage"]["attempts_aligned"])
        self.assertIsNone(result["usage"]["known_core_unknown_provider"])

    def test_rehashed_operation_reordering_is_rejected(self):
        self.records[2]["id"] = 7
        self.write_frames()
        with self.assertRaisesRegex(AuditError, "operation order"):
            self.audit()

    def test_event_loss_and_changed_outcome_are_rejected(self):
        self.events[0]["outputLossIncidents"] = 1
        self.write_events()
        with self.assertRaisesRegex(AuditError, "lost"):
            self.audit()
        self.events[0]["outputLossIncidents"] = 0
        self.events[0]["data"] = {"final": {"answer": "changed"}}
        self.write_events()
        with self.assertRaisesRegex(AuditError, "outcome"):
            self.audit()

    def test_artifact_bytes_and_metadata_are_verified(self):
        ref = {"id": "a-"+"1"*64, "sha256": hashlib.sha256(b"output").hexdigest(),
               "storedBytes": 6, "totalBytes": 6, "truncated": False, "label": "stdout"}
        self.state["artifacts"] = [ref]
        artifacts = self.session / "artifacts"
        artifacts.mkdir()
        blob = artifacts / (ref["id"] + ".blob")
        metadata = blob.with_suffix(".json")
        blob.write_bytes(b"output"); metadata.write_text(json.dumps(ref))
        self.assertEqual(self.audit()["verified_artifacts"], 1)
        blob.write_bytes(b"forged")
        with self.assertRaisesRegex(AuditError, "hash"):
            self.audit()
        blob.write_bytes(b"output"); metadata.write_text("{}")
        with self.assertRaisesRegex(AuditError, "metadata"):
            self.audit()


if __name__ == "__main__":
    unittest.main()
