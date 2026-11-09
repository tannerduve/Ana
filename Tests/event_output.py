"""CLI output backpressure and approval visibility with real pipes and terminals."""
import fcntl
import json
import os
from pathlib import Path
import pty
import subprocess
import sys
import tempfile
import termios
import unittest

from integration import response

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / ".lake/build/bin/harness"


class EventOutput(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.workspace = self.root / "workspace"
        self.workspace.mkdir()
        self.session = self.root / "session"

    def command(self, script, *, events=True, commands="deny"):
        config = self.root / "config.json"
        config.write_text(json.dumps({"model": "scripted", "commands": commands,
                                     "maxContextBytes": 2000000}))
        source = self.root / "script.json"
        source.write_text(json.dumps(script))
        args = [str(BIN), "run", "--workspace", str(self.workspace), "--config", str(config),
                "--task", "exercise output", "--script", str(source), "--session", str(self.session)]
        return args + (["--json"] if events else [])

    def inspect(self):
        result = subprocess.run([str(BIN), "inspect", str(self.session)],
                                capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        return json.loads(result.stdout)

    def test_unread_event_pipe_does_not_block_work_or_terminal_persistence(self):
        calls = [(f"write-{i}", "create", {"path": f"file-{i}", "content": "x" * 1500}) for i in range(24)]
        process = subprocess.Popen(self.command([response(calls), response(text="saved")]),
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            # Deliberately do not drain either pipe until the agent has exited.
            self.assertEqual(process.wait(timeout=10), 74)
            for i in range(24):
                self.assertEqual((self.workspace / f"file-{i}").read_text(), "x" * 1500)
            state = self.inspect()
            self.assertTrue(state["terminal"])
            self.assertEqual(state["state"]["toolDispatches"], 24)
            resumed = subprocess.run([str(BIN), "resume", str(self.session)],
                                     capture_output=True, text=True, timeout=10)
            self.assertEqual(resumed.returncode, 0, resumed.stderr)
            self.assertIn("saved", resumed.stdout)
            self.assertEqual(self.inspect()["state"]["toolDispatches"], 24)
        finally:
            if process.poll() is None:
                process.kill(); process.wait(timeout=3)
            process.stdout.close(); process.stderr.close()

    def test_closed_event_pipe_preserves_task_outcome(self):
        process = subprocess.Popen(self.command([response(text="saved despite closed consumer")]),
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        process.stdout.close()
        try:
            self.assertEqual(process.wait(timeout=5), 74)
            self.assertTrue(self.inspect()["terminal"])
        finally:
            if process.poll() is None:
                process.kill(); process.wait(timeout=3)
            process.stderr.close()

    def test_shared_regular_output_keeps_diagnostics_and_answer(self):
        path = self.root / "combined.log"
        with path.open("wb") as output:
            process = subprocess.run(self.command([response(text="FINAL-ANSWER")], events=False),
                                     stdout=output, stderr=subprocess.STDOUT, timeout=5)
        self.assertEqual(process.returncode, 0)
        text = path.read_text()
        self.assertIn("[0] intent\n", text)
        self.assertIn("finished\nFINAL-ANSWER\n", text)

    def test_terminal_control_bytes_are_not_rendered(self):
        answer = "visible\x1b[2J\rhidden\x07\x9bkeep\n"
        result = subprocess.run(self.command([response(text=answer)], events=False),
                                capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        for character in ["\x1b", "\r", "\x07", "\x9b"]:
            self.assertNotIn(character, result.stdout)
        self.assertIn("visible", result.stdout)
        # Rendering is separate from the authoritative transcript.
        history = self.inspect()["state"]["history"]
        self.assertEqual(history[-1]["content"][0]["text"], answer)

    def _approval(self, *, hidden=False, oversized=False, extra_args=()):
        argv = [sys.executable, "-c", "from pathlib import Path; Path('approved').write_text('yes')"]
        argv += list(extra_args)
        if oversized:
            argv += ["x" * 1000] * 150
        command = self.command([response([("command", "process", {"argv": argv})]), response()],
                               events=False, commands="ask")
        master, slave = pty.openpty()

        def controlling_terminal():
            os.setsid()
            fcntl.ioctl(0, termios.TIOCSCTTY, 0)
            if hidden:
                os.close(2)

        process = subprocess.Popen(command, stdin=slave, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   preexec_fn=controlling_terminal)
        os.close(slave)
        try:
            os.write(master, b"yes\n")
            out, err = process.communicate(timeout=8)
            return process.returncode, out, err
        finally:
            os.close(master)
            if process.poll() is None:
                process.kill(); process.wait(timeout=3)

    def test_visible_prompt_accepts_exact_terminal_answer(self):
        code, out, err = self._approval()
        self.assertEqual(code, 0, out + err)
        self.assertEqual((self.workspace / "approved").read_text(), "yes")
        self.assertEqual(self.inspect()["state"]["toolDispatches"], 1)

    def test_approval_metadata_escapes_controls_without_changing_the_operation(self):
        renamed = self.root / "workspace\n\u202ereordered\u202c"
        self.workspace.rename(renamed)
        self.workspace = renamed
        arguments = ["C1:\u009b2J", "BIDI:\u202erm\u202c", "invisible:\u200b", "emoji:🙂",
                     "DEL:\x7f", r"literal:\u202e"]
        code, out, err = self._approval(extra_args=arguments)
        self.assertEqual(code, 0, out + err)
        displayed = err.split(b"Approve this one operation?\n", 1)[1].split(b"Type yes to approve: ", 1)[0]
        self.assertTrue(displayed.isascii(), displayed)
        self.assertNotIn(b"\x7f", displayed)
        decoded = json.loads(displayed)
        self.assertEqual(decoded["workspace"], str(self.workspace))
        self.assertEqual(decoded["profile"], "host")
        self.assertEqual(decoded["arguments"]["argv"][-len(arguments):], arguments)
        self.assertEqual((self.workspace / "approved").read_text(), "yes")
        history = self.inspect()["state"]["history"]
        self.assertEqual(history[1]["content"][0]["input"]["argv"][-len(arguments):], arguments)

    def test_closed_diagnostic_sink_cannot_accept_preentered_approval(self):
        code, out, err = self._approval(hidden=True)
        self.assertEqual(code, 130, out + err)
        self.assertFalse((self.workspace / "approved").exists())
        self.assertEqual(self.inspect()["state"]["toolDispatches"], 0)

    def test_dropped_oversized_arguments_cannot_accept_preentered_approval(self):
        code, out, err = self._approval(oversized=True)
        self.assertEqual(code, 130, out + err)
        self.assertFalse((self.workspace / "approved").exists())
        self.assertEqual(self.inspect()["state"]["toolDispatches"], 0)


if __name__ == "__main__":
    unittest.main()
