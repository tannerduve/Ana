"""Independent positive/negative controls for the post-run continuation auditor."""
import copy
import gzip
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "runner"))
from audit_continuation import (APPLICATION_SUMMARY_INSTRUCTION, AuditError, SUMMARY_INSTRUCTION,
                               audit_run, budget_message, compact, repair_message, text_block, timeout_result)
from request_evidence import outbound_evidence


def write_frames(path, records):
    frames, previous = [], ""
    for index, record in enumerate(records):
        base = {"v": 1, "seq": index, "previous": previous, "record": record}
        checksum = hashlib.sha256(compact(base).encode()).hexdigest()
        frames.append({**base, "checksum": checksum})
        previous = checksum
    path.write_text("".join(compact(frame) + "\n" for frame in frames))


def recorded_schema7(directory, name="schema7-coding"):
    """Exact real CLI bytes; never execute saved candidate/fixture source.

    The captured child used scripted replies, not a provider. Its separate
    synthetic broker/checker rows exercise audit arithmetic only; they are not
    transport, billing, or task-quality evidence. The capture script and exact
    source/binary hashes are retained alongside the unchanged journal bytes.
    """
    path = Path(__file__).parent / "fixtures" / (name + ".json.gz")
    fixture = json.loads(gzip.decompress(path.read_bytes()))
    provenance = fixture["provenance"]
    assert hashlib.sha256(fixture["capture_script"].encode()).hexdigest() == provenance["capture_script_sha256"]
    for relative, value in fixture["files"].items():
        assert not Path(relative).is_absolute() and ".." not in Path(relative).parts
        assert hashlib.sha256(value.encode()).hexdigest() == provenance["file_sha256"][relative]
        target = directory / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(value)
    return (directory / "coding-three-turns", json.loads((directory / "broker.json").read_text()),
            json.loads((directory / "plan.json").read_text()), provenance)


def fixture(directory, schema=2, with_artifact=False, large=False, repair=None, transient=False, timed_out=False):
    (directory / "sessions/session").mkdir(parents=True)
    config = {"model": "scripted", "instructions": "Follow the fixed task.", "maxOutputTokens": 4096,
              "maxContextBytes": 65536, "maxSummaryBytes": 6000}
    if schema >= 3:
        config.update(maxArtifactBytes=1024, maxSessionArtifactBytes=2048)
    if schema >= 4:
        config.update(maxResponseRepairs=2, maxModelAttempts=20, maxRetries=1)
    if schema in [5, 7]:
        config.update(executionProfile="bubblewrap", operationTimeoutMs=90000,
                      maxToolOutputBytes=1024, maxToolCalls=10)
    artifacts = []
    records = [{"kind": "initial", "schema": schema, "implementation": "test-binary", "session": "test-session",
                "config": config, "task": "repair source"}]
    schemas = None
    if schema == 7:
        captured = json.loads(gzip.decompress((Path(__file__).parent / "fixtures/schema7-coding.json.gz").read_bytes()))
        raw_schemas = captured["files"]["schemas.json"]
        schemas = json.loads(raw_schemas)
        (directory.parent / "schemas.json").write_text(raw_schemas)
        records[0].update(application="coding", applicationVersion=1)
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
                "maxTokens": 4096, "purpose": purpose,
                **({"tools": schemas if purpose == "task" else []} if schema == 7 else {})}

    def task_context():
        messages = history if view is None else [view["summary"]] + history[view["sourceEnd"]:]
        if artifacts:
            messages = [{"role": "user", "content": [text_block(
                "Retained tool output artifacts (use artifact with an ID and byte range to read):\n" + compact(artifacts))]}] + messages
        if schema == 7:
            messages = messages + [budget_message(config, model_count + 1, tool_count, 4)]
        return messages

    def task(text="", call_id=None):
        messages = task_context()
        call = None if call_id is None else {"id": call_id, "name": "read", "input": {"path": "source.txt"}}
        returned = response(text, call)
        if timed_out and call_id == "read-1":
            assert schema in [5, 7]
            returned = {**returned, "content": [
                {"type": "tool_use", "id": "read-1", "name": "process", "input": {"argv": ["sh", "-c", "write_then_wait"]}},
                {"type": "tool_use", "id": "skip-create", "name": "create", "input": {"path": "skip", "content": "must not run"}},
                {"type": "tool_use", "id": "skip-read", "name": "read", "input": {"path": "skip"}}]}
            returned["calls"] = [{key: block[key] for key in ("id", "name", "input")} for block in returned["content"]]
        effect({"kind": "model", "request": request(messages, "task")}, {"success": {"response": returned}})
        history.append({"role": "assistant", "content": returned["content"]})

    def read(call_id):
        value = {"text": "observed file contents", "exitCode": None, "artifact": None, "sha256": None}
        if schema >= 3:
            del value["artifact"]
            value["artifacts"] = []
            if with_artifact and not artifacts:
                artifacts.append({"id": "a-"+"1"*64, "sha256": hashlib.sha256(b"artifact").hexdigest(),
                                  "storedBytes": 8, "totalBytes": 8, "label": "output", "truncated": False})
                value["artifacts"] = copy.deepcopy(artifacts)
            if large and call_id == "read-1":
                value["text"] = "x"*35000
        call = {"id": call_id, "operation": {"readFile": {"args": {"path": "source.txt", "startLine": 1, "endLine": 200}}}}
        if timed_out and call_id == "read-1":
            call["operation"] = {"runProcess": {"args": {"argv": ["sh", "-c", "write_then_wait"], "cwd": "."}}}
            value.update(text="partial output: αβγ", exitCode=137, sha256="f" * 64)
            effect({"kind": "tool", "call": call}, {"timedOut": {"partialResult": copy.deepcopy(value)}})
            normalized = {**value, "exitCode": None, "sha256": None, "text":
                "Command time limit reached; the sandboxed attempt has stopped. Partial effects may remain. "
                "Inspect the workspace and retained output before requesting more work.\npartial output: αβγ"}
            history.append({"role": "user", "content": [
                {"type": "tool_result", "tool_use_id": call_id, "content": compact(normalized), "is_error": True},
                *[{"type": "tool_result", "tool_use_id": skip,
                   "content": "not executed: previous command timed out; inspect its partial effects before requesting more work",
                   "is_error": True} for skip in ["skip-create", "skip-read"]]]})
            return
        effect({"kind": "tool", "call": call}, {"success": {"result": value}})
        history.append({"role": "user", "content": [{"type": "tool_result", "tool_use_id": call_id,
                        "content": compact(value), "is_error": False}]})

    def summarize(end, text):
        nonlocal view
        start, previous = (0, None) if view is None else (view["sourceEnd"], view["summary"])
        source = {"sourceStart": start, "sourceEnd": end, "previousSummary": previous}
        messages = ([previous] if previous else []) + history[start:end] + [
            {"role": "user", "content": [text_block(APPLICATION_SUMMARY_INSTRUCTION if schema == 7 else SUMMARY_INSTRUCTION)]}]
        returned = response(text)
        effect({"kind": "model", "request": request(messages, "summary")}, {"success": {"response": returned}})
        summaries.append({"plan": source, "response": returned})
        view = {"sourceEnd": end, "summary": {"role": "user", "content": [
            text_block("Continuation summary (may be incomplete):\n" + text)]}}

    control(); task(call_id="read-1"); control(); read("read-1"); control()
    if transient:
        effect({"kind": "model", "request": request(task_context(), "task")},
               {"failure": {"kind": "transport", "message": "connection lost"}})
        effect({"kind": "wait", "milliseconds": 1000}, "elapsed")
        control()
    if repair:
        assert schema >= 4
        invalid = response(call={"id": "discarded", "name": "read", "input": {}})
        if repair == "truncated":
            invalid["stop"] = "maxTokens"
        observation = ({"failure": {"kind": "malformed", "message": "incomplete stream"}}
                       if repair == "malformed" else {"success": {"response": invalid}})
        effect({"kind": "model", "request": request(task_context(), "task")}, observation)
        history.append(repair_message(repair, schema))
        control()
    control()
    summarize(1, "first summary"); control()
    checkpoint = {"nextId": operation, "modelAttempts": model_count + 1, "toolDispatches": tool_count}
    events.append({"event": "suspended", "operation": operation, "phase": "model", "data": {"durableCompletions": 8}})
    task(call_id="read-2"); control(); read("read-2"); control(); control()
    summarize(3, "second summary"); control(); task("done")
    outcome = {"final": {"answer": "done"}}
    records.append({"kind": "terminal", "id": operation, "outcome": outcome})
    events.append({"event": "finished", "operation": operation, "phase": {"stopped": {"outcome": outcome}}, "data": outcome})
    state = {"schemaVersion": schema, "sessionId": "test-session", "config": config, "history": history,
             "activeView": view, "pendingSummary": None, "summaries": summaries,
             "phase": {"stopped": {"outcome": outcome}}, "nextId": operation,
             "modelAttempts": model_count, "toolDispatches": tool_count,
             "seenCallIds": (["read-1", "skip-create", "skip-read", "read-2"] if timed_out else ["read-1", "read-2"]),
             "knownInputTokens": (model_count - (repair == "malformed") - transient) * 10,
             "knownOutputTokens": (model_count - (repair == "malformed") - transient) * 3,
             "unknownUsage": int(repair == "malformed") + int(transient)}
    if schema >= 4:
        state["responseRepairs"] = int(repair is not None)
    if schema >= 3:
        state["artifacts"] = artifacts
        for event in events:
            event["outputLossIncidents"] = 0
            if len(compact(event["data"]).encode()) > 32768:
                event["data"] = {"omitted": True, "reason": "event payload exceeds 32768 bytes; inspect the journal"}
    result = {"success": True, "checker": {"passed": True}, "replay_matches": True,
              "model_attempts": model_count, "tool_dispatches": tool_count,
              "provider_attempts": model_count, "unknown_usage_requests": 0,
              "accounted_usd": model_count * 0.0001, "durable_checkpoints": [checkpoint]}
    inspection = {"state": state, "pending": False, "terminal": True}
    plan = {"binary_sha256": "test-binary"}
    if schema == 7:
        state.update(turn=0, grant=None)
        inspection.update(application="coding", applicationVersion=1)
        checkpoint["turn"] = 0
        for event in events: event["turn"] = 0
        plan.update(task_context_version=4,
                    tool_schemas_sha256=hashlib.sha256(raw_schemas.encode()).hexdigest())
    (directory / "inspection.json").write_text(json.dumps(inspection))
    (directory / "result.json").write_text(json.dumps(result))
    (directory / "events.jsonl").write_text("".join(json.dumps(event) + "\n" for event in events))
    (directory / "resources.jsonl").write_text('Command exited with non-zero status 75\n{"peak_rss_kib":1}\n{"peak_rss_kib":1}\n')
    write_frames(directory / "sessions/session/journal.jsonl", records)
    broker = {"prices_per_million": {"input": 4, "output": 20, "cache_read": 0.2, "cache_write": 5},
              "records": [{"run_id": directory.name, "usage": {"input_tokens": 10, "output_tokens": 3},
                           "charged_usd": 0.0001, "reserved_usd": 1, "active": False} for _ in range(model_count)]}
    if schema >= 4:
        for index, charge in enumerate(broker["records"], 1):
            charge["attempt"] = index
    return broker, plan, records


class ContinuationAudit(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.directory = Path(self.temporary.name)
        self.broker, self.plan, self.records = fixture(self.directory)

    def tearDown(self):
        self.temporary.cleanup()

    def test_valid_trace_reconstructs_context_and_restart(self):
        report = audit_run(self.directory, self.broker, self.plan)
        self.assertEqual(report["request_evidence"]["status"], "unavailable_legacy")
        self.assertEqual(report["successful_summaries"], 2)
        self.assertEqual(report["post_summary_restart_operations"], [8])
        self.assertEqual(report["model_attempts"], 5)

    def test_recorded_schema7_three_turns_compaction_and_actual_restart(self):
        run, broker, plan, provenance = recorded_schema7(self.directory / "actual")
        journal = run / "sessions/session/journal.jsonl"
        before = hashlib.sha256(journal.read_bytes()).hexdigest()
        report = audit_run(run, broker, plan)
        self.assertEqual((report["user_turns"], report["declared_followups"], report["successful_summaries"],
                          report["model_attempts"], report["tool_dispatches"]), (3, 2, 5, 11, 3))
        self.assertEqual(report["post_summary_restart_operations"], [8])
        self.assertEqual(report["process_invocations"], 4)
        self.assertEqual(report["request_evidence"]["status"], "unavailable_legacy")
        self.assertEqual(provenance["binary_sha256"], plan["binary_sha256"])
        self.assertEqual(before, hashlib.sha256(journal.read_bytes()).hexdigest())

    def test_schema7_checkpoint_requires_exact_integer_turn(self):
        run, broker, plan, _ = recorded_schema7(self.directory / "turn-checkpoint")
        path = run / "result.json"
        original = json.loads(path.read_text())
        checkpoint = original["durable_checkpoints"][0]
        for value in [None, True, checkpoint["turn"] + 1]:
            changed = copy.deepcopy(original)
            if value is None:
                del changed["durable_checkpoints"][0]["turn"]
            else:
                changed["durable_checkpoints"][0]["turn"] = value
            path.write_text(json.dumps(changed))
            with self.subTest(turn=value), self.assertRaisesRegex(AuditError, "checkpoint turn identity differs"):
                audit_run(run, broker, plan)

    def test_recorded_cancelled_turn_is_reconstructed_without_inventing_compaction(self):
        run, broker, plan, _ = recorded_schema7(self.directory / "cancelled", "schema7-cancelled")
        with self.assertRaisesRegex(AuditError, "strict gate requires two accepted summaries"):
            audit_run(run, broker, plan)

    def test_schema7_requires_explicit_context_application_and_schema_binding(self):
        run, broker, plan, _ = recorded_schema7(self.directory / "actual")
        with self.assertRaisesRegex(AuditError, "context_version4"):
            audit_run(run, broker, {**plan, "task_context_version": 3})
        with self.assertRaisesRegex(AuditError, "schema export"):
            audit_run(run, broker, {**plan, "tool_schemas_sha256": "0" * 64})
        journal = run / "sessions/session/journal.jsonl"
        original = [json.loads(line)["record"] for line in journal.read_text().splitlines()]
        for change, expected in [("application", "application identity"), ("tools", "tool schemas"),
                                 ("summary", "summary-purpose instruction"), ("notice", "task context reconstruction")]:
            with self.subTest(change=change):
                records = copy.deepcopy(original)
                if change == "application":
                    records[0]["application"] = "inventory"
                else:
                    request = next(r["action"]["request"] for r in records if r["kind"] == "intent" and
                                   r["action"]["kind"] == "model" and
                                   r["action"]["request"]["purpose"] == ("summary" if change == "summary" else "task"))
                    if change == "tools": request["tools"] = []
                    elif change == "summary": request["messages"][-1]["content"][0]["text"] = SUMMARY_INSTRUCTION
                    else: request["messages"][-1]["content"][0]["text"] = request["messages"][-1]["content"][0]["text"].replace("operation", "command")
                write_frames(journal, records)
                with self.assertRaisesRegex(AuditError, expected): audit_run(run, broker, plan)

    def test_schema7_turns_cannot_be_hidden_reordered_or_refund_counters(self):
        run, broker, plan, _ = recorded_schema7(self.directory / "actual")
        with self.assertRaisesRegex(AuditError, "undeclared"):
            audit_run(run, broker, {key: value for key, value in plan.items() if key != "user_turns"})
        journal = run / "sessions/session/journal.jsonl"
        original = [json.loads(line)["record"] for line in journal.read_text().splitlines()]
        reset = copy.deepcopy(original)
        first_turn = next(r["id"] for r in reset if r["kind"] == "user_turn")
        request = next(r["action"]["request"] for r in reset if r["kind"] == "intent" and r["id"] > first_turn and
                       r["action"]["kind"] == "model" and r["action"]["request"]["purpose"] == "task")
        request["messages"][-1] = budget_message(original[0]["config"], 1, 0, 4)
        write_frames(journal, reset)
        with self.assertRaisesRegex(AuditError, "task context reconstruction"):
            audit_run(run, broker, plan)
        for field, value in [("turn", 2), ("turn", True), ("task", "new unapproved instruction"), ("id", 0)]:
            with self.subTest(field=field, value=value):
                records = copy.deepcopy(original)
                next(r for r in records if r["kind"] == "user_turn")[field] = value
                write_frames(journal, records)
                with self.assertRaises(AuditError): audit_run(run, broker, plan)
        records = copy.deepcopy(original)
        records.remove(next(r for r in records if r["kind"] == "terminal"))
        write_frames(journal, records)
        with self.assertRaisesRegex(AuditError, "unsettled or ineligible"):
            audit_run(run, broker, plan)
        write_frames(journal, original)
        path = run / "inspection.json"
        inspection = json.loads(path.read_text())
        for field in ["modelAttempts", "toolDispatches", "knownInputTokens", "nextId", "turn"]:
            changed = copy.deepcopy(inspection)
            changed["state"][field] -= 1
            path.write_text(json.dumps(changed))
            with self.subTest(field=field), self.assertRaises(AuditError): audit_run(run, broker, plan)

    def test_schema7_generic_repairs_and_settled_timeout_keep_history_and_artifacts(self):
        for repair in [None, "invalidBatch", "truncated", "malformed"]:
            with self.subTest(repair=repair):
                directory = self.directory / (repair or "timeout")
                directory.mkdir()
                broker, plan, records = fixture(directory, schema=7, with_artifact=True,
                                                repair=repair, timed_out=True)
                report = audit_run(directory, broker, plan)
                self.assertEqual(report["response_repairs"], int(repair is not None))
                self.assertEqual(report["timed_out_tools"], 1)
                self.assertEqual(report["skipped_tool_call_ids"], ["skip-create", "skip-read"])
                if repair == "invalidBatch":
                    inspection_path = directory / "inspection.json"
                    inspection = json.loads(inspection_path.read_text())
                    history = inspection["state"]["history"]
                    index = history.index(repair_message(repair, 7))
                    history[index] = repair_message(repair, 5)
                    inspection_path.write_text(json.dumps(inspection))
                    with self.assertRaises(AuditError): audit_run(directory, broker, plan)

    def test_task_and_summary_context_digests_must_match_reconstruction(self):
        self.plan["request_evidence_version"] = 1
        with self.assertRaisesRegex(AuditError, "attempt order"):
            audit_run(self.directory, self.broker, self.plan)
        requests = [r["action"]["request"] for r in self.records
                    if r["kind"] == "intent" and r["action"]["kind"] == "model"]
        for index, (request, charge) in enumerate(zip(requests, self.broker["records"]), 1):
            raw = json.dumps(request).encode()
            charge.update(outbound_evidence(raw)[1], request_bytes=len(raw), attempt=index)
        report = audit_run(self.directory, self.broker, self.plan)
        self.assertEqual(report["request_evidence"]["matched_contexts"], 5)
        for index in [0, 1, 2]:  # initial task, summary, resumed task
            original = self.broker["records"][index]["system_messages_sha256"]
            self.broker["records"][index]["system_messages_sha256"] = "0" * 64
            with self.assertRaisesRegex(AuditError, "system/messages differ"):
                audit_run(self.directory, self.broker, self.plan)
            self.broker["records"][index]["system_messages_sha256"] = original

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

    def test_schema3_artifacts_large_events_and_json_invocation_records(self):
        directory = self.directory / "modern"
        directory.mkdir()
        broker, plan, records = fixture(directory, schema=3, with_artifact=True, large=True)
        (directory / "events.jsonl").rename(directory / "events.log")
        (directory / "resources.jsonl").write_text('{"exit_code":75}\n{"exit_code":0}\n')
        self.assertEqual(audit_run(directory, broker, plan)["successful_summaries"], 2)
        # Registry authority survives summaries; changing only a resumed catalog
        # must fail even with valid frame checksums and unchanged result metadata.
        for record in records:
            if record["kind"] == "intent" and record["id"] == 8:
                record["action"]["request"]["messages"][0]["content"][0]["text"] = "unregistered artifact"
        write_frames(directory / "sessions/session/journal.jsonl", records)
        with self.assertRaisesRegex(AuditError, "task context reconstruction"):
            audit_run(directory, broker, plan)

    def test_schema4_repairs_reconstruct_context_without_accepting_rejected_calls(self):
        for kind in ["invalidBatch", "truncated", "malformed"]:
            with self.subTest(kind=kind):
                directory = self.directory / kind
                directory.mkdir()
                broker, plan, _ = fixture(directory, schema=4, repair=kind, with_artifact=True)
                report = audit_run(directory, broker, plan)
                self.assertEqual(report["response_repairs"], 1)
                self.assertEqual(report["tool_dispatches"], 2)
                self.assertEqual(report["unknown_core_known_provider"], int(kind == "malformed"))
                path = directory / "inspection.json"
                state = json.loads(path.read_text())
                state["state"]["responseRepairs"] = 0
                path.write_text(json.dumps(state))
                with self.assertRaisesRegex(AuditError, "response-repair counter"):
                    audit_run(directory, broker, plan)

    def test_schema4_repair_observation_and_usage_cannot_be_relabelled(self):
        directory = self.directory / "repair-negative"
        directory.mkdir()
        broker, plan, records = fixture(directory, schema=4, repair="malformed")
        broker["records"][0]["usage"]["input_tokens"] += 1
        with self.assertRaisesRegex(AuditError, "corresponding journal completion"):
            audit_run(directory, broker, plan)
        broker["records"][0]["usage"]["input_tokens"] -= 1
        for record in records:
            if record["kind"] == "completion" and "failure" in record["observation"]:
                record["observation"]["failure"]["kind"] = "authentication"
        write_frames(directory / "sessions/session/journal.jsonl", records)
        with self.assertRaisesRegex(AuditError, "context reconstruction"):
            audit_run(directory, broker, plan)

    def test_transient_failure_does_not_consume_later_repair_feedback(self):
        for kind in ["invalidBatch", "truncated", "malformed"]:
            with self.subTest(kind=kind):
                directory = self.directory / ("transient-" + kind)
                directory.mkdir()
                broker, plan, _ = fixture(directory, schema=4, repair=kind,
                                           transient=True, with_artifact=True)
                report = audit_run(directory, broker, plan)
                self.assertEqual(report["response_repairs"], 1)
                self.assertEqual(report["successful_summaries"], 2)
                self.assertEqual(report["tool_dispatches"], 2)
                self.assertEqual(report["unknown_core_known_provider"], 1 + (kind == "malformed"))

    def test_schema4_attempt_ordinals_cannot_be_missing_or_reordered(self):
        directory = self.directory / "ordinal-negative"
        directory.mkdir()
        broker, plan, _ = fixture(directory, schema=4)
        for change in ["missing", "duplicate", "mismatch", "reordered", "boolean"]:
            with self.subTest(change=change):
                modified = copy.deepcopy(broker)
                rows = modified["records"]
                if change == "missing":
                    del rows[0]["attempt"]
                elif change == "duplicate":
                    rows[1]["attempt"] = rows[0]["attempt"]
                elif change == "mismatch":
                    rows[0]["attempt"] = 99
                elif change == "reordered":
                    rows[0], rows[1] = rows[1], rows[0]
                else:
                    rows[0]["attempt"] = True
                with self.assertRaisesRegex(AuditError, "provider attempts are missing, duplicated or reordered"):
                    audit_run(directory, modified, plan)

    def test_historical_attempt_ordinals_are_optional_but_must_be_consistent(self):
        for schema in [2, 3]:
            with self.subTest(schema=schema):
                directory = self.directory / ("legacy-" + str(schema))
                directory.mkdir()
                broker, plan, _ = fixture(directory, schema=schema)
                audit_run(directory, broker, plan)
                for index, row in enumerate(broker["records"], 1):
                    row["attempt"] = index
                audit_run(directory, broker, plan)
                del broker["records"][1]["attempt"]
                with self.assertRaisesRegex(AuditError, "provider attempts are missing, duplicated or reordered"):
                    audit_run(directory, broker, plan)


    def test_v3_review_pending_does_not_block_continuation_audit(self):
        directory = self.directory / "review-pending"
        directory.mkdir()
        broker, plan, _ = fixture(directory, schema=4, repair="malformed", with_artifact=True)
        path = directory / "result.json"
        result = json.loads(path.read_text())
        result.update(qualification_version=3, qualification_status="pending_independent_review",
                      success=False, exit_code=0)
        result["checker"]["resolved"] = True
        path.write_text(json.dumps(result))
        original = path.read_bytes()
        report = audit_run(directory, broker, plan)
        self.assertEqual(report["status"], "passed")
        self.assertEqual(report["successful_summaries"], 2)
        self.assertEqual(report["post_summary_restart_operations"], [10])
        self.assertEqual(report["response_repairs"], 1)
        self.assertEqual(path.read_bytes(), original)
        self.assertFalse(json.loads(path.read_text())["success"])

    def test_v3_cached_success_cannot_override_failed_execution_or_checker(self):
        directory = self.directory / "review-prerequisites"
        directory.mkdir()
        broker, plan, _ = fixture(directory, schema=4)
        path = directory / "result.json"
        original = json.loads(path.read_text())
        original.update(qualification_version=3, success=True, exit_code=0,
                        normal_finish=True, artifact_pass=True)
        original["checker"]["resolved"] = True
        for change in ["nonzero-exit", "boolean-exit", "missing-exit", "checker-failed", "proof-failed"]:
            with self.subTest(change=change):
                result = copy.deepcopy(original)
                if change == "nonzero-exit":
                    result["exit_code"] = 1
                elif change == "boolean-exit":
                    result["exit_code"] = False
                elif change == "missing-exit":
                    del result["exit_code"]
                elif change == "checker-failed":
                    result["checker"]["resolved"] = False
                else:
                    result["checker"]["additional_proof_integrity"] = False
                path.write_text(json.dumps(result))
                with self.assertRaisesRegex(AuditError, "finish normally with an independent checker pass"):
                    audit_run(directory, broker, plan)

    def test_schema5_timeout_closes_full_batch_without_dispatching_suffix(self):
        directory = self.directory / "timeout"
        directory.mkdir()
        broker, plan, records = fixture(directory, schema=5, timed_out=True, with_artifact=True)
        original = (directory / "inspection.json").read_bytes()
        report = audit_run(directory, broker, plan)
        self.assertEqual((report["timed_out_tools"], report["tool_dispatches"]), (1, 2))
        self.assertEqual(report["skipped_tool_call_ids"], ["skip-create", "skip-read"])
        self.assertEqual((directory / "inspection.json").read_bytes(), original)
        requests = [r["action"]["request"] for r in records if r["kind"] == "intent" and
                    r["action"]["kind"] == "model" and r["action"]["request"]["purpose"] == "task"]
        block = next(block for message in requests[1]["messages"] for block in message["content"]
                     if block.get("tool_use_id") == "read-1")
        payload = json.loads(block["content"])
        self.assertIsNone(payload["exitCode"])
        self.assertIsNone(payload["sha256"])
        self.assertTrue(block["is_error"])
        self.assertEqual(len(payload["artifacts"]), 1)

    def test_timeout_cannot_be_relabelled_as_legacy_host_or_file_observation(self):
        for mode in ["legacy", "host", "file", "missing-partial"]:
            with self.subTest(mode=mode):
                directory = self.directory / mode
                directory.mkdir()
                broker, plan, records = fixture(directory, schema=5, timed_out=True)
                path = directory / "inspection.json"
                inspection = json.loads(path.read_text())
                if mode == "legacy":
                    inspection["state"]["schemaVersion"] = records[0]["schema"] = 4
                elif mode == "host":
                    inspection["state"]["config"]["executionProfile"] = records[0]["config"]["executionProfile"] = "host"
                elif mode == "file":
                    call = next(r["action"]["call"] for r in records if r["kind"] == "intent" and r["action"]["kind"] == "tool")
                    call["operation"] = {"readFile": {"args": {"path": "source.txt", "startLine": 1, "endLine": 200}}}
                else:
                    completion = next(r for r in records if r["kind"] == "completion" and "timedOut" in r["observation"])
                    completion["observation"] = {"timedOut": {}}
                path.write_text(json.dumps(inspection))
                write_frames(directory / "sessions/session/journal.jsonl", records)
                with self.assertRaisesRegex(AuditError, "interrupted tool|settled-timeout tool|typed timeout"):
                    audit_run(directory, broker, plan)

    def test_timeout_result_order_flags_exit_hash_and_dispatch_counters_are_checked(self):
        for mode in ["order", "is-error", "exit", "sha", "text", "dispatch", "debit"]:
            with self.subTest(mode=mode):
                directory = self.directory / ("tamper-" + mode)
                directory.mkdir()
                broker, plan, records = fixture(directory, schema=5, timed_out=True)
                path = directory / "inspection.json"
                inspection = json.loads(path.read_text())
                if mode == "dispatch":
                    tools = [r["action"]["call"] for r in records if r["kind"] == "intent" and r["action"]["kind"] == "tool"]
                    tools[1]["id"] = "skip-create"
                elif mode == "debit":
                    inspection["state"]["toolDispatches"] += 2
                    path.write_text(json.dumps(inspection))
                else:
                    blocks = inspection["state"]["history"][2]["content"]
                    if mode == "order":
                        blocks[1], blocks[2] = blocks[2], blocks[1]
                    elif mode == "is-error":
                        blocks[1]["is_error"] = False
                    elif mode == "text":
                        blocks[1]["content"] = "executed successfully"
                    else:
                        payload = json.loads(blocks[0]["content"])
                        payload["exitCode" if mode == "exit" else "sha256"] = 137 if mode == "exit" else "f" * 64
                        blocks[0]["content"] = compact(payload)
                    path.write_text(json.dumps(inspection))
                write_frames(directory / "sessions/session/journal.jsonl", records)
                with self.assertRaisesRegex(AuditError, "history differs|tool dispatch|out of admitted order"):
                    audit_run(directory, broker, plan)

    def test_timeout_partial_metadata_is_all_or_nothing_and_utf8_bounded(self):
        config = {"maxToolOutputBytes": 1024, "maxArtifactBytes": 1024, "maxSessionArtifactBytes": 2048}
        reference = {"id": "a-" + "1" * 64, "sha256": "2" * 64, "label": "stdout",
                     "storedBytes": 1, "totalBytes": 1, "truncated": False}
        prefix = ("Command time limit reached; the sandboxed attempt has stopped. Partial effects may remain. "
                  "Inspect the workspace and retained output before requesting more work.\n")
        result, registry = timeout_result(config, None, [])
        self.assertEqual(result, {"text": prefix, "exitCode": None, "sha256": None, "artifacts": []})
        self.assertEqual(registry, [])
        partial = {"text": "αβγ", "exitCode": 137, "sha256": "f" * 64, "artifacts": [reference]}
        result, registry = timeout_result({**config, "maxToolOutputBytes": len(prefix.encode()) + 3}, partial, [])
        self.assertEqual(result["text"], prefix + "α")
        self.assertEqual(registry, [reference])
        for mode, refs, existing, message in [
            ("count", [reference] * 3, [], "tool returned too many artifact references"),
            ("metadata", [reference, {**reference, "label": "invalid"}], [], "invalid artifact metadata"),
            ("identity", [{**reference, "totalBytes": 2, "truncated": True}], [reference], "artifact identity changed"),
            ("allowance", [{**reference, "storedBytes": 1024, "totalBytes": 1024}], [], "session artifact allowance exhausted")]:
            with self.subTest(mode=mode):
                limits = {**config, "maxSessionArtifactBytes": 100 if mode == "allowance" else 2048}
                value, kept = timeout_result(limits, {**partial, "artifacts": refs}, existing)
                self.assertEqual(value["artifacts"], [])
                self.assertEqual(kept, existing)
                self.assertEqual(value["text"], "Artifact references rejected: " + message + "\n" + prefix + "αβγ")
                self.assertIsNone(value["exitCode"])
                self.assertIsNone(value["sha256"])


if __name__ == "__main__":
    unittest.main()
