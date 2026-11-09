"""Offline stop/capture/delete ordering and partial-evidence regressions."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "runner"))
import public_bench as public


class InterruptedEvidence(unittest.TestCase):
    def test_invocation_diagnostic_write_cannot_replace_keyboard_interrupt(self):
        for failed_path in ["resources.jsonl", "events.log"]:
            with self.subTest(path=failed_path), tempfile.TemporaryDirectory() as temporary:
                output = Path(temporary)
                interruption = KeyboardInterrupt()
                original_open = Path.open
                def failed_open(path, mode="r", *args, **kwargs):
                    if path.name == failed_path and mode in ("a", "ab"):
                        raise OSError("injected diagnostic write failure")
                    return original_open(path, mode, *args, **kwargs)
                def invocation(*args, **kwargs):
                    kwargs["output"].write_bytes(b"retained provisional events\n")
                    raise interruption
                with patch.object(public, "docker", side_effect=invocation), \
                     patch.object(Path, "open", new=failed_open):
                    with self.assertRaises(KeyboardInterrupt) as caught:
                        public.run_invocations("owned", ["exec"], None, output, 10)
                self.assertIs(caught.exception, interruption)
                self.assertIn("Invocation diagnostic write failed: OSError", interruption.__notes__)
                self.assertEqual((output / "invocation-000.jsonl").read_bytes(), b"retained provisional events\n")

    def exercise(self, *, session_error=False, workspace_error=False, stop_error=False, timeout=False,
                 metadata_error=False, capture_interrupt=None):
        calls = []
        class Broker:
            records = []
            def add_run(self, *args): return "http://127.0.0.1/fixture/v1/messages"
            def close_run(self, *args): calls.append("settle")
            def admission_refusal(self, *args): return None

        def docker(*args, **kwargs):
            if args[0] == "stop":
                calls.append("stop")
                if stop_error: raise RuntimeError("cannot establish stopped state")
            if args[0] == "rm": calls.append("forced-delete")
            return SimpleNamespace(returncode=0, stdout="")

        def mirror(container, source, target):
            self.assertIn("stop", calls)
            self.assertNotIn("delete", calls)
            calls.append("session")
            if capture_interrupt == "session" and calls.count("session") == 1:
                raise KeyboardInterrupt()
            if session_error: raise ValueError("untrusted session symlink")
            target.mkdir()
            (target / "journal.jsonl").write_bytes(b"retained-session\n")
            return {"entries": 1}

        def capture(container, workspace, target, baseline):
            self.assertIn("stop", calls)
            self.assertNotIn("delete", calls)
            calls.append("workspace")
            if capture_interrupt == "workspace" and calls.count("workspace") == 1:
                raise KeyboardInterrupt()
            if workspace_error: raise ValueError("candidate archive unavailable")
            target.mkdir()
            saved = target / "candidate.patch"
            saved.write_bytes(b"retained nonempty patch\n")
            return {"patch_path": str(saved), "changed_paths": ["source.py"], "existing_changed_paths": ["source.py"]}

        def deleted(container): calls.append("delete")
        args = SimpleNamespace(model="fixture", max_attempts=2, max_tools=2, context_bytes=30000,
            timeout=10, prepared_bwrap=None, harness_root=ROOT.parent, cohort="test", attempt=1,
            apt_https=False, apt_main_only=False)
        failure = subprocess.TimeoutExpired("fixture", 10) if timeout else KeyboardInterrupt()
        def invocation(container, first, resume, output, timeout, **kwargs):
            if capture_interrupt:
                return {"exit_code": 0}
            if metadata_error:
                (output / "resources.jsonl").write_bytes(b'{"unfinished":')
            raise failure
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.object(public, "harness_binary", return_value=root / "unused"), \
                 patch.object(public, "eval_tools_binary", return_value=root / "unused"), \
                 patch.object(public, "node_identity", return_value={"root": str(root)}), \
                 patch.object(public, "validate_node_preflight", return_value={"status": "fixture"}), \
                 patch.object(public, "create_container", return_value="exact-owned-container"), \
                 patch.object(public, "capture_baseline", return_value={"baseline_tree": "baseline"}), \
                 patch.object(public, "assert_space"), patch.object(public, "docker", side_effect=docker), \
                 patch.object(public, "run_invocations", side_effect=invocation), \
                 patch.object(public, "mirror_session_after_stop", side_effect=mirror), \
                 patch.object(public, "capture_candidate_after_stop", side_effect=capture), \
                 patch.object(public, "remove_container", side_effect=deleted), \
                 patch.object(public, "ACTIVE_OWNER", None), \
                 patch.object(public, "ContainerMemory") as memory, \
                 patch.object(public, "swe_verify") as grader:
                memory.return_value.start.return_value.stop.return_value = {"unavailable_reason": "fixture"}
                task = {"id": "fixture", "repository_task": True, "benchmark": "fixture",
                        "workspace": "/workspace", "image_digest": "fixture"}
                if timeout:
                    public.run_one(task, "pi", 0, [], args, root, Broker(), task_text="fixture")
                else:
                    with self.assertRaises(KeyboardInterrupt):
                        public.run_one(task, "pi", 0, [], args, root, Broker(), task_text="fixture")
                grader.assert_not_called()
            paths = list(root.glob("*/result.json"))
            self.assertEqual(len(paths), 1)
            record = json.loads(paths[0].read_text())
            run = paths[0].parent
            self.assertFalse(record["success"])
            self.assertFalse(record["normal_finish"])
            self.assertLess(calls.index("stop"), calls.index("settle"))
            if stop_error:
                self.assertNotIn("session", calls)
                self.assertNotIn("workspace", calls)
                self.assertNotIn("candidate_patch_sha256", record)
                self.assertFalse((run / "candidate.patch").exists())
            else:
                self.assertLess(calls.index("session"), calls.index("delete"))
                self.assertLess(calls.index("workspace"), calls.index("delete"))
                if not session_error:
                    self.assertEqual((run / "sessions/journal.jsonl").read_bytes(), b"retained-session\n")
                if not workspace_error:
                    raw = (run / "candidate.patch").read_bytes()
                    self.assertEqual(raw, b"retained nonempty patch\n")
                    self.assertEqual(record["candidate_patch_sha256"], hashlib.sha256(raw).hexdigest())
                else:
                    self.assertNotIn("candidate_patch_sha256", record)
                    self.assertFalse((run / "candidate.patch").exists())
                if capture_interrupt == "workspace":
                    self.assertEqual(calls.count("session"), 1, "completed session capture must not be overwritten")
            return record

    def test_keyboard_interrupt_retains_both_before_delete_then_reraises(self):
        record = self.exercise()
        self.assertTrue(record["interrupted"])
        self.assertEqual(record["interruption"], "KeyboardInterrupt")
        self.assertEqual(record["evidence_capture"]["workspace"]["status"], "captured")
        self.assertEqual(record["evidence_capture"]["session"]["status"], "captured")
        self.assertFalse(record.get("evidence_capture_unsettled", False))

    def test_corrupt_diagnostic_does_not_swallow_interrupt(self):
        record = self.exercise(metadata_error=True)
        self.assertTrue(record["interrupted"])
        self.assertIn("JSONDecodeError", record["invocation_metadata_error"])
        self.assertEqual(record["evidence_capture"]["workspace"]["status"], "captured")

    def test_interrupt_during_capture_preserves_completed_and_remaining_evidence(self):
        for stage in ["session", "workspace"]:
            with self.subTest(stage=stage):
                record = self.exercise(capture_interrupt=stage)
                self.assertTrue(record["interrupted"])
                self.assertEqual(record["evidence_capture"]["workspace"]["status"], "captured")
                self.assertEqual(record["evidence_capture"]["session"]["status"], "captured")

    def test_session_failure_still_retains_workspace(self):
        record = self.exercise(session_error=True)
        self.assertTrue(record["evidence_capture_unsettled"])
        self.assertEqual(record["evidence_capture"]["workspace"]["status"], "captured")
        self.assertEqual(record["evidence_capture"]["session"]["status"], "unavailable")

    def test_workspace_failure_still_retains_session_and_never_fabricates_empty_patch(self):
        record = self.exercise(workspace_error=True)
        self.assertTrue(record["evidence_capture_unsettled"])
        self.assertEqual(record["evidence_capture"]["workspace"]["status"], "unavailable")
        self.assertEqual(record["evidence_capture"]["session"]["status"], "captured")

    def test_failed_stop_forces_owned_removal_without_unsafe_capture(self):
        record = self.exercise(stop_error=True)
        self.assertTrue(record["evidence_capture_unsettled"])
        self.assertEqual(record["evidence_capture"]["workspace"]["status"], "unavailable")

    def test_timeout_retains_bytes_without_grading(self):
        record = self.exercise(timeout=True)
        self.assertTrue(record["timed_out"])
        self.assertEqual(record["evidence_capture"]["workspace"]["status"], "captured")
        self.assertEqual(record["evidence_capture"]["session"]["status"], "captured")


if __name__ == "__main__":
    unittest.main()
