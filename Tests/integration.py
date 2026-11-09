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

    def run_script(self, script, expected=0):
        cfg = self.root / "config.json"
        cfg.write_text(json.dumps(self.config))
        scripted = self.root / "script.json"
        scripted.write_text(json.dumps(script))
        return self.cli("run", "--workspace", self.ws, "--config", cfg,
                        "--task", "repair the program and test it", "--session", self.session,
                        "--script", scripted, "--json", expected=expected)

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


if __name__ == "__main__":
    unittest.main(verbosity=2)
