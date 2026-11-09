"""Real CLI/file/process/journal tests, with scripted complete model messages.
No provider credentials or live quality claims. All workspaces are temporary.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
import journal_fixture as helper
from provider_streaming import event
BIN = ROOT / ".lake/build/bin/harness"


def response(calls=(), text="done", stop=None):
    return {"type": "message", "role": "assistant",
            "stop_reason": stop or ("tool_use" if calls else "end_turn"),
            "content": [{"type": "tool_use", "id": ident, "name": name, "input": args}
                        for ident, name, args in calls] or [{"type": "text", "text": text}],
            "usage": {"input_tokens": 20, "output_tokens": 10}}


class Integration(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.ws = self.root / "workspace"
        self.ws.mkdir()
        self.session = self.root / "session"
        self.config = {"model": "scripted-test", "workspace": str(self.ws), "commands": "allow"}

    def cli(self, *args, expected=0):
        result = subprocess.run([str(BIN), *map(str, args)], cwd=self.root,
                                text=True, capture_output=True, timeout=30)
        self.assertEqual(result.returncode, expected, result.stderr + result.stdout)
        return result

    def run_script(self, script, expected=0, extra=()):
        cfg = self.root / "config.json"
        cfg.write_text(json.dumps(self.config))
        scripted = self.root / "script.json"
        scripted.write_text(json.dumps(script))
        return self.cli("run", "--workspace", self.ws, "--config", cfg,
                        "--task", "repair the program and test it", "--session", self.session,
                        "--script", scripted, "--json", *extra, expected=expected)

    def inspect(self):
        return json.loads(self.cli("inspect", self.session).stdout)

    def rewrite_prefix(self, frames):
        path = self.session / "journal.jsonl"
        path.unlink()
        for record in frames:
            helper.journal_append(str(path), record)

    def test_read_edit_test_and_replay(self):
        before = 'def add(a, b):\n    return a - b\n'
        program = self.ws / "calc.py"
        program.write_text(before)
        script = [response([("read1", "read", {"path": "calc.py"})]),
                  response([("edit1", "edit", {"path": "calc.py", "old": "a - b", "new": "a + b",
                              "expectedSha256": hashlib.sha256(before.encode()).hexdigest()}),
                            ("test1", "process", {"argv": [sys.executable, "-c",
                              "from calc import add; assert add(2,3)==5; print('regression passed')"]})]),
                  response(text="Fixed addition and ran the regression test.")]
        result = self.run_script(script)
        events = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual(events[-1]["event"], "finished")
        self.assertIn("a + b", program.read_text())
        loaded = self.inspect()
        self.assertTrue(loaded["terminal"])
        self.assertEqual(loaded["state"]["modelAttempts"], 3)
        self.assertEqual(loaded["state"]["toolDispatches"], 3)
        self.assertIn("regression passed", json.dumps(loaded))
        saved = (self.session / "journal.jsonl").read_bytes()
        self.cli("replay", self.session)
        self.cli("resume", self.session)
        self.assertEqual(saved, (self.session / "journal.jsonl").read_bytes())

    def test_malformed_later_call_prevents_earlier_mutation(self):
        self.run_script([response([("one", "create", {"path": "bad", "content": "bad"}),
                                   ("two", "unknown", {})])], expected=1)
        self.assertFalse((self.ws / "bad").exists())
        self.assertEqual(self.inspect()["state"]["toolDispatches"], 0)

    def test_rejected_batch_can_be_corrected_after_durable_restart(self):
        self.config["maxResponseRepairs"] = 1
        rejected = response([("discarded", "create", {"path": "bad", "content": "bad"}),
                             ("invalid", "unknown", {})])
        corrected = response([("corrected", "create", {"path": "result", "content": "fixed"})])
        self.run_script([rejected, corrected, response()], expected=75,
                        extra=("--yield-after", "2"))
        before = self.inspect()["state"]
        self.assertEqual((before["modelAttempts"], before["toolDispatches"], before["responseRepairs"]), (1, 0, 1))
        self.assertEqual(before["seenCallIds"], [])
        self.assertFalse((self.ws / "bad").exists())
        self.assertEqual(json.loads(self.cli("replay", self.session).stdout)["state"], before)
        self.cli("resume", self.session)
        after = self.inspect()["state"]
        self.assertEqual((after["modelAttempts"], after["toolDispatches"], after["responseRepairs"]), (3, 1, 1))
        self.assertEqual(after["seenCallIds"], ["corrected"])
        self.assertEqual((after["knownInputTokens"], after["knownOutputTokens"]), (60, 30))
        self.assertEqual((self.ws / "result").read_text(), "fixed")
        self.assertFalse((self.ws / "bad").exists())

    def test_restart_cannot_refund_response_repair_allowance(self):
        self.config["maxResponseRepairs"] = 1
        rejected = response([("discarded", "create", {"path": "bad", "content": "bad"}),
                             ("invalid", "unknown", {})])
        self.run_script([rejected, rejected, response()], expected=75,
                        extra=("--yield-after", "2"))
        before = self.inspect()["state"]
        self.cli("resume", self.session, expected=1)
        after = self.inspect()["state"]
        self.assertEqual((after["modelAttempts"], after["toolDispatches"], after["responseRepairs"]), (2, 0, 1))
        self.assertEqual(after["history"], before["history"])
        self.assertFalse((self.ws / "bad").exists())

    def test_malformed_stream_repairs_without_accepting_its_complete_earlier_call(self):
        import http.server
        import threading
        from provider_streaming import header, terminal

        def tool(index, ident, path):
            return (event("content_block_start", index=index, content_block={
                "type": "tool_use", "id": ident, "name": "create", "input": {}}) +
                event("content_block_delta", index=index, delta={"type": "input_json_delta",
                    "partial_json": json.dumps({"path": path, "content": "observed"})}) +
                event("content_block_stop", index=index))

        malformed = (header() + tool(0, "discarded", "bad") +
            event("content_block_start", index=1, content_block={"type": "text", "text": ""}) +
            terminal("tool_use"))  # The second block was never closed.
        corrected = header() + tool(0, "corrected", "result") + terminal("tool_use")
        final = (header() + event("content_block_start", index=0,
            content_block={"type": "text", "text": "done"}) +
            event("content_block_stop", index=0) + terminal())
        requests = []

        class Handler(http.server.BaseHTTPRequestHandler):
            def log_message(self, *_):
                pass

            def do_POST(self):
                requests.append(json.loads(self.rfile.read(int(self.headers["Content-Length"]))))
                body = [malformed, corrected, final][min(len(requests) - 1, 2)]
                self.send_response(200)
                self.send_header("Content-Type", "text/event-stream")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

        server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.addCleanup(server.server_close)
        self.addCleanup(server.shutdown)
        threading.Thread(target=server.serve_forever, daemon=True).start()
        self.config.update(testEndpoint=f"http://127.0.0.1:{server.server_port}/messages",
                           maxModelAttempts=4, maxToolCalls=4, maxRetries=0, maxResponseRepairs=1)
        cfg = self.root / "config.json"
        cfg.write_text(json.dumps(self.config))
        self.cli("run", "--workspace", self.ws, "--config", cfg,
                 "--task", "create result", "--session", self.session, "--json")
        self.assertEqual(len(requests), 3)
        self.assertEqual([m["role"] for m in requests[1]["messages"]], ["user", "user", "user"])
        self.assertIn("[Harness validation feedback]", requests[1]["messages"][1]["content"][0]["text"])
        self.assertTrue(requests[1]["messages"][2]["content"][0]["text"].startswith(
            "[Harness limits] After this request, at most 2 further model requests and 4 tool executions remain."))
        self.assertNotIn("discarded", json.dumps(requests[1]["messages"]))
        self.assertFalse((self.ws / "bad").exists())
        self.assertEqual((self.ws / "result").read_text(), "observed")
        state = self.inspect()["state"]
        self.assertEqual((state["modelAttempts"], state["toolDispatches"], state["responseRepairs"]), (3, 1, 1))
        self.assertEqual(state["unknownUsage"], 1)
        self.assertEqual(state["seenCallIds"], ["corrected"])
        self.assertEqual(json.loads(self.cli("replay", self.session).stdout)["state"], state)

    def test_standalone_binary_without_python_or_repository_runtime(self):
        # No helper source is copied and PATH contains no Python (or other program).
        import shutil
        binary = self.root / "harness"
        shutil.copy2(BIN, binary)
        empty_path = self.root / "empty-path"
        empty_path.mkdir()
        cfg = self.root / "standalone-config.json"
        cfg.write_text(json.dumps(self.config))
        script = self.root / "standalone-script.json"
        script.write_text(json.dumps([
            response([("create", "create", {"path": "result", "content": "native IO"})]),
            response([("check", "process", {"argv": ["/bin/sh", "-c", "test -f result && printf verified"]})]),
            response(text="done")]))
        env = {**os.environ, "PATH": str(empty_path)}
        result = subprocess.run([str(binary), "run", "--workspace", str(self.ws), "--config", str(cfg),
                                 "--task", "standalone test", "--session", str(self.session), "--script", str(script)],
                                env=env, text=True, capture_output=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertEqual((self.ws / "result").read_text(), "native IO")
        replay = subprocess.run([str(binary), "replay", str(self.session)], env=env,
                                text=True, capture_output=True, timeout=15)
        self.assertEqual(replay.returncode, 0, replay.stderr)
        self.assertIn("verified", replay.stdout)

    def test_resume_rejects_inconsistent_model_observation(self):
        self.run_script([response(text="done")])
        frames = helper.journal_read(self.session / "journal.jsonl")["records"]
        index = next(i for i, record in enumerate(frames)
                     if record.get("kind") == "intent"
                     and record["action"]["kind"] == "model")
        observed = frames[index + 1]["observation"]["success"]["response"]
        # A validly framed, typed completion bypasses provider normalization.
        # The proposed call is absent from its authoritative content blocks.
        observed["stop"] = "toolUse"
        observed["calls"] = [{"id": "injected", "name": "create",
                              "input": {"path": "bad", "content": "unexpected"}}]
        self.rewrite_prefix(frames[:index + 2])

        self.cli("resume", self.session, expected=1)
        self.assertFalse((self.ws / "bad").exists())
        state = self.inspect()["state"]
        self.assertEqual(state["modelAttempts"], 1)
        self.assertEqual(state["toolDispatches"], 0)
        self.assertEqual(state["knownInputTokens"], 20)
        self.assertEqual(state["knownOutputTokens"], 10)
        self.assertEqual(state["unknownUsage"], 0)
        self.assertEqual(state["seenCallIds"], [])
        self.assertEqual(len(state["history"]), 1)
        saved = helper.journal_read(self.session / "journal.jsonl")["records"]
        self.assertFalse(any(record.get("kind") == "intent"
                             and record["action"]["kind"] == "tool"
                             for record in saved))

    def test_truncation_executes_nothing(self):
        self.run_script([response([("one", "create", {"path": "bad", "content": "bad"})], stop="max_tokens")], expected=1)
        self.assertFalse((self.ws / "bad").exists())

    def test_budget_and_context(self):
        self.config["maxModelAttempts"] = 0
        self.run_script([response()], expected=3)
        self.assertEqual(self.inspect()["state"]["modelAttempts"], 0)

    def test_context_ceiling(self):
        self.config["maxContextBytes"] = 1
        self.run_script([response()], expected=3)
        self.assertEqual(self.inspect()["state"]["modelAttempts"], 0)

    def test_completed_prefix_resumes_without_redoing_mutation(self):
        self.run_script([response([("one", "create", {"path": "once", "content": "original"})]), response()])
        frames = helper.journal_read(self.session / "journal.jsonl")["records"]
        # Keep the durable tool completion, discard subsequent records to simulate crash.
        index = next(i for i, r in enumerate(frames) if r.get("kind") == "intent"
                     and r["action"]["kind"] == "tool")
        self.rewrite_prefix(frames[:index + 2])
        (self.ws / "once").write_text("external change")
        self.cli("resume", self.session)
        self.assertEqual((self.ws / "once").read_text(), "external change")

    def test_uncertain_mutation_never_reruns(self):
        self.run_script([response([("one", "create", {"path": "once", "content": "original"})]), response()])
        frames = helper.journal_read(self.session / "journal.jsonl")["records"]
        index = next(i for i, r in enumerate(frames) if r.get("kind") == "intent"
                     and r["action"]["kind"] == "tool")
        self.rewrite_prefix(frames[:index + 1])
        self.assertTrue(self.inspect()["pending"])
        before = (self.session / "journal.jsonl").read_bytes()
        self.cli("resume", self.session, expected=2)
        self.assertEqual(before, (self.session / "journal.jsonl").read_bytes())

    def test_single_writer_lock(self):
        import fcntl
        self.run_script([response()])
        with open(self.session / "lock", "a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            self.cli("resume", self.session, expected=2)

    def test_interrupted_tail_preserved(self):
        self.run_script([response()])
        with open(self.session / "journal.jsonl", "ab") as output:
            output.write(b'{"incomplete"')
        self.assertTrue(self.inspect()["interruptedStorage"])
        self.cli("resume", self.session, expected=2)

    def test_cancel_active_process(self):
        cfg = self.root / "config.json"
        cfg.write_text(json.dumps(self.config))
        script = self.root / "script.json"
        script.write_text(json.dumps([response([("long", "process", {"argv": [sys.executable, "-c",
            "import time; open('started','w').close(); time.sleep(30)"]})]), response()]))
        process = subprocess.Popen([str(BIN), "run", "--workspace", str(self.ws), "--config", str(cfg),
            "--task", "run command", "--session", str(self.session), "--script", str(script)],
            cwd=self.root, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            deadline = time.monotonic() + 10
            while not (self.ws / "started").exists():
                self.assertIsNone(process.poll(), "runner exited before command started")
                self.assertLess(time.monotonic(), deadline)
                time.sleep(0.02)
            self.cli("cancel", self.session)
            out, err = process.communicate(timeout=10)
            self.assertEqual(process.returncode, 4, out + err)
            self.assertEqual(self.inspect()["state"]["toolDispatches"], 1)
        finally:
            if process.poll() is None:
                process.kill()
                process.communicate()

    def test_denied_command_does_not_dispatch(self):
        self.config["commands"] = "deny"
        self.run_script([response([("one", "process", {"argv": [sys.executable, "-c", "open('bad','w').write('bad')"]})]), response()])
        self.assertFalse((self.ws / "bad").exists())
        self.assertEqual(self.inspect()["state"]["toolDispatches"], 0)

    def test_yield_is_a_durable_boundary_with_preserved_reservations(self):
        self.run_script([response([("one", "create", {"path": "once", "content": "original"})]),
                         response(text="done")], expected=75, extra=("--yield-after", "3"))
        before = self.inspect()
        self.assertFalse(before["pending"])
        self.assertFalse(before["terminal"])
        self.assertEqual(before["state"]["modelAttempts"], 1)
        self.assertEqual(before["state"]["toolDispatches"], 1)
        self.assertFalse((self.ws / "once").exists())
        records = helper.journal_read(self.session / "journal.jsonl")["records"]
        self.assertEqual(records[-1]["kind"], "completion")
        self.cli("resume", self.session)
        after = self.inspect()
        self.assertEqual(after["state"]["modelAttempts"], 2)
        self.assertEqual(after["state"]["toolDispatches"], 1)
        self.assertEqual((self.ws / "once").read_text(), "original")
        self.assertEqual(json.loads(self.cli("replay", self.session).stdout), after)

    def test_compaction_crosses_a_durable_restart_boundary(self):
        # Requests now account for the actual offered tool schemas. Keep the
        # trigger between the first and second large result, as this fixture intends.
        self.config.update(maxContextBytes=35000, compactAtPercent=85,
                           compactionKeepMessages=2, maxSummaryBytes=2000)
        (self.ws / "large.txt").write_text("repository fact " + "x" * 3900)
        scripted = [response([("read1", "read", {"path": "large.txt"})]),
                    response([("read2", "read", {"path": "large.txt"})]),
                    response(text="The file was inspected twice; continue with the requested final answer."),
                    response(text="Completed after compaction and restart.")]
        self.run_script(scripted, expected=75, extra=("--yield-after", "12"))
        before = self.inspect()
        self.assertEqual(len(before["state"]["summaries"]), 1)
        self.assertEqual(before["state"]["modelAttempts"], 3)
        self.assertEqual(before["state"]["toolDispatches"], 2)
        self.assertEqual(len(before["state"]["history"]), 5)
        self.assertFalse(before["pending"])
        self.assertFalse(before["terminal"])
        records = helper.journal_read(self.session / "journal.jsonl")["records"]
        summary = [r for r in records if r.get("kind") == "intent"
                   and r["action"].get("request", {}).get("purpose") == "summary"]
        self.assertEqual(len(summary), 1)
        self.cli("resume", self.session)
        after = self.inspect()
        self.assertEqual(after["state"]["modelAttempts"], 4)
        self.assertEqual(after["state"]["toolDispatches"], 2)
        self.assertEqual(after["state"]["summaries"], before["state"]["summaries"])
        self.assertEqual(after["state"]["history"][:5], before["state"]["history"])
        self.assertTrue(after["terminal"])
        self.assertEqual(json.loads(self.cli("replay", self.session).stdout), after)

    def test_frozen_loopback_provider_and_external_override_rejection(self):
        import http.server
        import threading
        bodies = []
        class Handler(http.server.BaseHTTPRequestHandler):
            def do_POST(handler):
                bodies.append(json.loads(handler.rfile.read(int(handler.headers["Content-Length"]))))
                message = response(text="loopback completed")
                data = (event("message_start", message={**message, "content": [], "stop_reason": None}) +
                        event("content_block_start", index=0, content_block=message["content"][0]) +
                        event("content_block_stop", index=0) +
                        event("message_delta", delta={"stop_reason": "end_turn"}, usage={"output_tokens": 10}) +
                        event("message_stop"))
                handler.send_response(200)
                handler.send_header("Content-Length", str(len(data)))
                handler.end_headers()
                handler.wfile.write(data)
            def log_message(self, *_):
                pass
        server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        self.addCleanup(server.server_close)
        self.addCleanup(server.shutdown)
        self.config["testEndpoint"] = f"http://127.0.0.1:{server.server_port}/messages"
        cfg = self.root / "provider-config.json"
        cfg.write_text(json.dumps(self.config))
        self.cli("run", "--workspace", self.ws, "--config", cfg, "--task", "answer",
                 "--session", self.session)
        self.assertEqual(len(bodies), 1)
        self.assertTrue(bodies[0]["stream"])
        self.assertEqual(self.inspect()["state"]["config"]["testEndpoint"], self.config["testEndpoint"])
        cfg.write_text(json.dumps({**self.config, "testEndpoint": "https://example.com/messages"}))
        self.cli("run", "--workspace", self.ws, "--config", cfg, "--task", "answer",
                 "--session", self.root / "rejected-session", expected=1)
        self.assertEqual(len(bodies), 1)

    def test_resolution_of_recorded_interruption_preserves_remaining_batch(self):
        self.config["operationTimeoutMs"] = 500
        self.run_script([response([
            ("partial", "process", {"argv": ["/bin/sh", "-c", "printf x >> once; sleep 5"]}),
            ("remaining", "create", {"path": "remaining", "content": "continued"})]),
            response(text="continued after explicit resolution")], expected=4)
        before = self.inspect()
        operation = before["recoverableOperation"]
        self.assertIsNotNone(operation)
        self.assertFalse(before["pending"])
        self.assertTrue(before["terminal"])
        self.assertFalse((self.ws / "remaining").exists())
        self.assertEqual((self.ws / "once").read_bytes(), b"x")
        self.cli("resolve", self.session, "--operation", str(operation), "--status", "abandoned",
                 "--note", "Observed partial output; original process group was terminated",
                 "--resources-settled")
        self.cli("resume", self.session)
        after = self.inspect()
        self.assertEqual((self.ws / "once").read_bytes(), b"x")
        self.assertEqual((self.ws / "remaining").read_text(), "continued")
        self.assertEqual(after["state"]["toolDispatches"], 2)
        self.assertEqual(after["state"]["modelAttempts"], 2)


if __name__ == "__main__":
    unittest.main(verbosity=2)
