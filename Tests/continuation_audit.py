"""Independent positive/negative controls for the post-run continuation auditor."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "eval/runner"))
from audit_continuation import AuditError, SUMMARY_INSTRUCTION, audit_run, compact, text_block


def write_frames(path, records):
    frames, previous = [], ""
    for index, record in enumerate(records):
        base = {"v": 1, "seq": index, "previous": previous, "record": record}
        checksum = hashlib.sha256(compact(base).encode()).hexdigest()
        frames.append({**base, "checksum": checksum})
        previous = checksum
    path.write_text("".join(compact(frame) + "\n" for frame in frames))


def fixture(directory):
    (directory / "sessions/session").mkdir(parents=True)
    config = {"model": "scripted", "instructions": "Follow the fixed task.", "maxOutputTokens": 4096,
              "maxContextBytes": 65536, "maxSummaryBytes": 6000}
    records = [{"kind": "initial", "schema": 2, "implementation": "test-binary", "session": "test-session",
                "config": config, "task": "repair source"}]
    history = [{"role": "user", "content": [text_block("repair source")]}]
    events, summaries, view, operation = [], [], None, 0
    model_count = tool_count = 0

    def effect(action, observation):
        nonlocal operation, model_count, tool_count
        kind = action["kind"]
        phase = "summary" if kind == "model" and action["request"]["purpose"] == "summary" else "model" if kind == "model" else "controlModel"
        for event, key, value in [("intent", "action", action), ("completion", "observation", observation)]:
            records.append(copy.deepcopy({"kind": event, "id": operation, key: value}))
            events.append(copy.deepcopy({"event": event, "operation": operation, "phase": phase, "data": value}))
        operation += 1
        model_count += kind == "model"
        tool_count += kind == "tool"

    def control():
        effect({"kind": "control"}, {"cancelled": False, "deadlineExceeded": False, "monotonicMs": 0})

    def response(text="", call=None):
        content = [text_block(text)] if call is None else [{"type": "tool_use", **call}]
        return {"content": content, "calls": [] if call is None else [call], "text": text,
                "stop": "endTurn" if call is None else "toolUse",
                "usage": {"inputTokens": 10, "outputTokens": 3, "raw": None}}

    def request(messages, purpose):
        return {"model": "scripted", "system": config["instructions"], "messages": messages,
                "maxTokens": 4096, "purpose": purpose}

    def task(text="", call_id=None):
        messages = history if view is None else [view["summary"]] + history[view["sourceEnd"]:]
        call = None if call_id is None else {"id": call_id, "name": "read", "input": {"path": "source.txt"}}
        returned = response(text, call)
        effect({"kind": "model", "request": request(messages, "task")}, {"success": {"response": returned}})
        history.append({"role": "assistant", "content": returned["content"]})

    def read(call_id):
        value = {"text": "observed file contents", "exitCode": None, "artifact": None, "sha256": None}
        call = {"id": call_id, "operation": {"readFile": {"args": {"path": "source.txt", "startLine": 1, "endLine": 200}}}}
        effect({"kind": "tool", "call": call}, {"success": {"result": value}})
        history.append({"role": "user", "content": [{"type": "tool_result", "tool_use_id": call_id,
                        "content": compact(value), "is_error": False}]})

    def summarize(end, text):
        nonlocal view
        start, previous = (0, None) if view is None else (view["sourceEnd"], view["summary"])
        source = {"sourceStart": start, "sourceEnd": end, "previousSummary": previous}
        messages = ([previous] if previous else []) + history[start:end] + [
            {"role": "user", "content": [text_block(SUMMARY_INSTRUCTION)]}]
        returned = response(text)
        effect({"kind": "model", "request": request(messages, "summary")}, {"success": {"response": returned}})
        summaries.append({"plan": source, "response": returned})
        view = {"sourceEnd": end, "summary": {"role": "user", "content": [
            text_block("Continuation summary (may be incomplete):\n" + text)]}}

    control(); task(call_id="read-1"); control(); read("read-1"); control(); control()
    summarize(1, "first summary"); control()
    checkpoint = {"nextId": operation, "modelAttempts": model_count + 1, "toolDispatches": tool_count}
    events.append({"event": "suspended", "operation": operation, "phase": "model", "data": {"durableCompletions": 8}})
    task(call_id="read-2"); control(); read("read-2"); control(); control()
    summarize(3, "second summary"); control(); task("done")
    outcome = {"final": {"answer": "done"}}
    records.append({"kind": "terminal", "id": operation, "outcome": outcome})
    events.append({"event": "finished", "operation": operation, "phase": {"stopped": {"outcome": outcome}}, "data": outcome})
    state = {"schemaVersion": 2, "sessionId": "test-session", "config": config, "history": history,
             "activeView": view, "pendingSummary": None, "summaries": summaries,
             "phase": {"stopped": {"outcome": outcome}}, "nextId": operation,
             "modelAttempts": model_count, "toolDispatches": tool_count, "seenCallIds": ["read-1", "read-2"],
             "knownInputTokens": model_count * 10, "knownOutputTokens": model_count * 3, "unknownUsage": 0}
    result = {"success": True, "checker": {"passed": True}, "replay_matches": True,
              "model_attempts": model_count, "tool_dispatches": tool_count,
              "provider_attempts": model_count, "unknown_usage_requests": 0,
              "accounted_usd": model_count * 0.0001, "durable_checkpoints": [checkpoint]}
    inspection = {"state": state, "pending": False, "terminal": True}
    (directory / "inspection.json").write_text(json.dumps(inspection))
    (directory / "result.json").write_text(json.dumps(result))
    (directory / "events.jsonl").write_text("".join(json.dumps(event) + "\n" for event in events))
    (directory / "resources.jsonl").write_text('Command exited with non-zero status 75\n{"peak_rss_kib":1}\n{"peak_rss_kib":1}\n')
    write_frames(directory / "sessions/session/journal.jsonl", records)
    broker = {"prices_per_million": {"input": 4, "output": 20, "cache_read": 0.2, "cache_write": 5},
              "records": [{"run_id": directory.name, "usage": {"input_tokens": 10, "output_tokens": 3},
                           "charged_usd": 0.0001, "reserved_usd": 1, "active": False} for _ in range(model_count)]}
    return broker, {"binary_sha256": "test-binary"}, records


class ContinuationAudit(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.directory = Path(self.temporary.name)
        self.broker, self.plan, self.records = fixture(self.directory)

    def tearDown(self):
        self.temporary.cleanup()

    def test_valid_trace_reconstructs_context_and_restart(self):
        report = audit_run(self.directory, self.broker, self.plan)
        self.assertEqual(report["successful_summaries"], 2)
        self.assertEqual(report["post_summary_restart_operations"], [8])
        self.assertEqual(report["model_attempts"], 5)

    def tamper_request(self, operation):
        for record in self.records:
            if record["kind"] == "intent" and record["id"] == operation:
                record["action"]["request"]["messages"][0]["content"][0]["text"] = "invented context"
        # Re-sign all frames: semantic checks must reject this, not just checksums.
        write_frames(self.directory / "sessions/session/journal.jsonl", self.records)

    def test_changed_summary_source_rejected_even_with_valid_checksums(self):
        self.tamper_request(6)
        with self.assertRaisesRegex(AuditError, "summary source reconstruction"):
            audit_run(self.directory, self.broker, self.plan)

    def test_changed_resumed_context_rejected_even_with_valid_checksums(self):
        self.tamper_request(8)
        with self.assertRaisesRegex(AuditError, "task context reconstruction"):
            audit_run(self.directory, self.broker, self.plan)

    def test_changed_counter_rejected(self):
        path = self.directory / "inspection.json"
        inspection = json.loads(path.read_text())
        inspection["state"]["modelAttempts"] += 1
        path.write_text(json.dumps(inspection))
        with self.assertRaisesRegex(AuditError, "model reservation count"):
            audit_run(self.directory, self.broker, self.plan)


if __name__ == "__main__":
    unittest.main()
