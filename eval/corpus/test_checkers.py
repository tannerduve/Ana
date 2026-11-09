#!/usr/bin/env python3
"""Negative controls for evaluator integrity, distinct from task quality tests."""
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import check


class CheckerIntegrity(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="corpus-integrity-")
        self.root = Path(self.temporary.name)

    def tearDown(self):
        self.temporary.cleanup()

    def solution(self, task_id):
        task = next(t for t in json.loads((check.ROOT / "manifest.json").read_text())["tasks"] if t["id"] == task_id)
        workspace = self.root / task_id
        shutil.copytree(check.ROOT / task["fixture"], workspace)
        for name in task["editable"]:
            shutil.copyfile(check.ROOT / task["reference"] / name, workspace / name)
        return workspace

    def test_visible_test_cannot_be_deleted_or_weakened(self):
        workspace = self.solution("dev05-version-order")
        (workspace / "test_public.py").write_text("# all tests removed\n")
        result = check.evaluate("dev05-version-order", workspace)
        self.assertFalse(result["passed"])
        self.assertEqual(result["failures"][0]["kind"], "immutable_modified")

    def test_readme_is_immutable(self):
        workspace = self.solution("dev02-config-overlay")
        (workspace / "README.md").write_text("new weaker requirements")
        self.assertFalse(check.evaluate("dev02-config-overlay", workspace)["passed"])

    def test_symlinked_candidate_is_rejected(self):
        workspace = self.solution("dev05-version-order")
        source = workspace / "versions.py"
        outside = self.root / "outside.py"
        source.rename(outside)
        source.symlink_to(outside)
        result = check.evaluate("dev05-version-order", workspace)
        self.assertEqual(result["failures"][0]["kind"], "invalid_source")

    def test_answer_type_and_input_mutation_are_checked(self):
        workspace = self.solution("dev02-config-overlay")
        (workspace / "overlay.py").write_text("def overlay(a,b):\n a.update(b)\n return a\n")
        self.assertFalse(check.evaluate("dev02-config-overlay", workspace)["passed"])

    def test_theorem_statement_cannot_be_weakened(self):
        workspace = self.solution("dev11-lean-reverse")
        source = workspace / "Proof.lean"
        source.write_text("import Definitions\ntheorem reverse_twice (xs : List Nat) : True := by trivial\n")
        result = check.evaluate("dev11-lean-reverse", workspace)
        self.assertEqual(result["failures"][0]["kind"], "theorem_statement_changed")

    def test_proof_placeholder_is_not_a_success(self):
        workspace = self.solution("dev11-lean-reverse")
        source = workspace / "Proof.lean"
        source.write_text(source.read_text().replace("  simp", "  sorry"))
        result = check.evaluate("dev11-lean-reverse", workspace)
        self.assertEqual(result["failures"][0]["kind"], "forbidden_proof_construct")

    def test_signature_in_comment_does_not_bypass_statement_check(self):
        workspace = self.solution("dev11-lean-reverse")
        source = workspace / "Proof.lean"
        old = source.read_text()
        source.write_text("/- " + old + " -/\nimport Definitions\ntheorem reverse_twice : True := by trivial\n")
        result = check.evaluate("dev11-lean-reverse", workspace)
        self.assertEqual(result["failures"][0]["kind"], "theorem_statement_changed")

    def test_unexpected_candidate_files_do_not_enter_checker_import_path(self):
        workspace = self.solution("dev05-version-order")
        (workspace / "json.py").write_text("raise RuntimeError('candidate shadowed checker JSON')\n")
        self.assertTrue(check.evaluate("dev05-version-order", workspace)["passed"])

    def test_corpus_split_and_continuation_claims(self):
        tasks = json.loads((check.ROOT / "manifest.json").read_text())["tasks"]
        self.assertEqual(sum(t["split"] == "development" for t in tasks), 12)
        self.assertEqual(sum(t["split"] == "reserved" for t in tasks), 4)
        long_tasks = [t for t in tasks if "sustained_context" in t["tags"]]
        self.assertEqual(len(long_tasks), 2)
        self.assertTrue(all(not t["sustained_acceptance"]["task_checker_alone_sufficient"] for t in long_tasks))


if __name__ == "__main__":
    unittest.main()
