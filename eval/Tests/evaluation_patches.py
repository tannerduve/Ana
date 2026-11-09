"""Independent negative controls for the read-only candidate patch auditor."""
import copy
import json
from pathlib import Path
import os
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "runner"))
from audit_patches import audit_run, audit_suite, digest, inventory


class PatchAudit(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.corpus = self.root / "corpus"
        fixture = self.corpus / "fixtures/task"
        fixture.mkdir(parents=True)
        for name, text in {"source.py": "def solve(x): return 0\n", "test_public.py": "assert True\n", "README.md": "Return the input.\n"}.items():
            (fixture / name).write_text(text)
        hashes = {path.name: digest(path.read_bytes()) for path in fixture.iterdir()}
        self.task = {"id": "task", "split": "reserved", "fixture": "fixtures/task", "editable": ["source.py"],
                     "immutable": ["test_public.py", "README.md"], "artifact_sha256": hashes}
        (self.corpus / "manifest.json").write_text(json.dumps({"tasks": [self.task]}))
        self.suite = self.root / "runs"
        self.directory = self.suite / "task-controlled-lean-0-id"
        self.directory.mkdir(parents=True)
        self.workspace = self.directory / "workspace"
        shutil.copytree(fixture, self.workspace)
        self.result = {"run_id": self.directory.name, "task_id": "task", "engine": "lean", "track": "controlled",
                       "repetition": 0, "success": True, "checker": {"passed": True, "candidate_sha256": copy.deepcopy(hashes)}}
        self.save_result()
        self.before_manifest = (self.corpus / "manifest.json").read_bytes()

    def save_result(self):
        (self.directory / "result.json").write_text(json.dumps(self.result))

    def tearDown(self):
        self.temp.cleanup()

    def audit(self):
        return audit_run(self.directory, self.task, self.corpus)

    def test_allowed_change_and_cache_are_inventory_not_score(self):
        path = self.workspace / "source.py"
        path.write_text("def solve(x): return x\n")
        self.result["checker"]["candidate_sha256"]["source.py"] = digest(path.read_bytes())
        self.save_result()
        (self.workspace / "__pycache__").mkdir()
        (self.workspace / "__pycache__/source.pyc").write_bytes(b"compiled")
        report = self.audit()
        self.assertEqual(report["issues"], [])
        self.assertEqual([item["path"] for item in report["allowed_source_changes"]], ["source.py"])
        self.assertTrue(all(item["classification"] == "generated_cache" for item in report["extras"]))
        self.assertEqual(report["manual_review"]["status"], "not_reviewed")
        self.assertEqual(self.before_manifest, (self.corpus / "manifest.json").read_bytes())

    def test_protected_edit_and_missing_source_are_visible(self):
        (self.workspace / "test_public.py").write_text("# removed checks\n")
        (self.workspace / "source.py").unlink()
        report = self.audit()
        self.assertEqual(report["missing_files"], ["source.py"])
        self.assertEqual(report["protected_changes"][0]["path"], "test_public.py")
        self.assertTrue(report["reported_success"])  # Auditor does not rewrite the recorded score.
        self.assertIn("checker_artifact_mismatch", {issue["kind"] for issue in report["issues"]})

    def test_symlink_file_and_directory_are_not_followed(self):
        outside = self.root / "private"
        outside.mkdir()
        (outside / "secret").write_text("not part of the candidate")
        (self.workspace / "source.py").unlink()
        (self.workspace / "source.py").symlink_to(outside / "secret")
        (self.workspace / "alias").symlink_to(outside, target_is_directory=True)
        report = self.audit()
        self.assertEqual({item["path"] for item in report["symlinks"]}, {"source.py", "alias"})
        self.assertFalse(any(item["path"] == "alias/secret" for item in report["extras"]))
        self.assertIsNone(report["allowed_source_changes"][0]["after_sha256"])

    def test_special_file_does_not_block_inventory(self):
        os.mkfifo(self.workspace / "fifo")
        report = self.audit()
        self.assertEqual(report["special_files"], ["fifo"])

    def test_static_flags_remain_unreviewed_hints(self):
        (self.workspace / "source.py").write_text("# A harmless documentation reference to /checker\n")
        report = self.audit()
        self.assertEqual(report["source_review_flags"], [{"path": "source.py", "line": 1, "kind": "checker_reference"}])
        self.assertEqual(report["manual_review"]["status"], "not_reviewed")
        self.assertTrue(report["reported_success"])

    def test_hardlinks_and_unexpected_extras_are_visible(self):
        os.link(self.workspace / "source.py", self.workspace / "alias.py")
        report = self.audit()
        self.assertEqual(set(report["hardlinks"]), {"source.py", "alias.py"})
        self.assertEqual(report["extras"][0]["classification"], "review")

    def test_size_limits_are_explicit_incomplete_inventory(self):
        with patch("audit_patches.MAX_FILE_BYTES", 4):
            report = self.audit()
        self.assertIn("content_limit", {item["kind"] for item in report["issues"]})
        self.assertEqual(report["manual_review"]["status"], "not_reviewed")

    def test_candidate_module_is_never_imported(self):
        marker = self.root / "executed"
        (self.workspace / "source.py").write_text(f"from pathlib import Path\nPath({str(marker)!r}).write_text('executed')\n")
        self.audit()
        self.assertFalse(marker.exists())

    def test_only_completed_runs_and_exact_snapshot_manual_reuse(self):
        (self.suite / "in-progress/workspace").mkdir(parents=True)
        report = audit_suite(self.suite, self.corpus)
        self.assertEqual(report["completed_runs"], 1)
        self.assertEqual(report["pending_directories"], ["in-progress"])
        report["runs"][0]["manual_review"] = {"status": "reviewed", "finding": "test"}
        same = audit_suite(self.suite, self.corpus, report)
        self.assertEqual(same["manual_reviewed_runs"], 1)
        (self.workspace / "source.py").write_text("changed after review")
        changed = audit_suite(self.suite, self.corpus, report)
        self.assertEqual(changed["manual_reviewed_runs"], 0)

    def test_manifest_drift_and_workspace_symlink_fail_closed(self):
        (self.suite / "plan.json").write_text(json.dumps({"manifest_sha256": "old"}))
        shutil.rmtree(self.workspace)
        self.workspace.symlink_to(self.corpus / "fixtures/task", target_is_directory=True)
        report = audit_suite(self.suite, self.corpus)
        self.assertIn("plan_manifest_mismatch", {item["kind"] for item in report["errors"]})
        self.assertIn("inventory_error", {item["kind"] for item in report["runs"][0]["issues"]})

    def test_complete_cohort_requires_all_planned_cells(self):
        plan = {"manifest_sha256": digest(self.before_manifest), "tasks": ["task"],
                "tracks": ["controlled"], "engines": ["lean", "pi"], "repetitions": 1}
        (self.suite / "plan.json").write_text(json.dumps(plan))
        report = audit_suite(self.suite, self.corpus)
        self.assertEqual(report["expected_runs"], 2)
        self.assertFalse(report["cohort_complete"])
        plan["engines"] = ["lean"]
        (self.suite / "plan.json").write_text(json.dumps(plan))
        self.assertTrue(audit_suite(self.suite, self.corpus)["cohort_complete"])

    def test_duplicate_run_is_not_counted_as_complete_cohort(self):
        plan = {"manifest_sha256": digest(self.before_manifest), "tasks": ["task"],
                "tracks": ["controlled"], "engines": ["lean"], "repetitions": 1}
        (self.suite / "plan.json").write_text(json.dumps(plan))
        duplicate = self.suite / "duplicate"
        shutil.copytree(self.directory, duplicate)
        result = copy.deepcopy(self.result)
        result["run_id"] = duplicate.name
        (duplicate / "result.json").write_text(json.dumps(result))
        report = audit_suite(self.suite, self.corpus)
        self.assertFalse(report["cohort_complete"])
        self.assertIn("duplicate_planned_run", {item["kind"] for item in report["errors"]})


if __name__ == "__main__":
    unittest.main()
