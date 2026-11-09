"""Prospective review binds exact evidence; historical results stay unchanged."""
import copy
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
import patch_review as review
import public_bench as public
import summarize_public


class PatchReview(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.run = Path(self.tmp.name)
        self.patch = b"diff --git a/tests/test_add.py b/tests/test_add.py\n+def test_new_case(): assert add(2, 3) == 5\n"
        (self.run / "candidate.patch").write_bytes(self.patch)
        self.record = {"qualification_version": 3, "run_id": "fixture", "engine": "lean", "success": False,
            "qualification_status": "pending_independent_review", "exit_code": 0,
            "checker": {"resolved": True}, "session_integrity": {"passed": True}, "unknown_usage_requests": 0,
            "user_task_sha256": "a" * 64, "candidate_patch_sha256": hashlib.sha256(self.patch).hexdigest(),
            "workspace_snapshot": {"candidate_tree": "b" * 40},
            "existing_test_files_modified": ["tests/test_add.py"]}
        self.save()

    def save(self):
        (self.run / "result.json").write_text(json.dumps(self.record))

    def approved(self):
        value = review.review_template(self.run)
        value.update(reviewer="independent fixture reviewer", independent_of_candidate=True,
                     decision="approve", rationale="Added a regression without changing existing assertions; checked full patch.")
        value["checks"] = dict.fromkeys(review.REVIEW_CHECKS, True)
        return value

    def test_added_regression_needs_review_and_preserves_original(self):
        raw = (self.run / "result.json").read_bytes()
        with self.assertRaisesRegex(ValueError, "explicit approve/reject"):
            review.qualify(self.run, review.review_template(self.run))
        self.assertTrue(review.qualify(self.run, self.approved())["qualified_success"])
        self.assertEqual((self.run / "result.json").read_bytes(), raw)
        self.assertFalse(json.loads(raw)["success"])

    def test_unchanged_tests_do_not_bypass_review(self):
        self.record["existing_test_files_modified"] = []
        self.save()
        value = self.approved()
        value["independent_of_candidate"] = False
        with self.assertRaisesRegex(ValueError, "independent evaluator"):
            review.qualify(self.run, value)

    def test_review_cannot_follow_patch_or_task_mutation(self):
        value = self.approved()
        (self.run / "candidate.patch").write_bytes(self.patch + b"-assert required_condition\n")
        with self.assertRaisesRegex(ValueError, "differs from the artifact"):
            review.qualify(self.run, value)
        (self.run / "candidate.patch").write_bytes(self.patch)
        self.record["user_task_sha256"] = "c" * 64
        self.save()
        with self.assertRaisesRegex(ValueError, "exact run"):
            review.qualify(self.run, value)

    def test_explicit_rejection_of_weakening_is_not_overruled_by_official_pass(self):
        value = self.approved()
        value.update(decision="reject", rationale="Existing unrelated assertion was removed.")
        value["checks"]["no_unrelated_test_weakening_or_deletion"] = False
        self.assertFalse(review.qualify(self.run, value)["qualified_success"])
        value["decision"] = "approve"
        self.assertFalse(review.qualify(self.run, value)["qualified_success"])

    def test_review_does_not_override_failed_execution_grading_or_accounting(self):
        original = copy.deepcopy(self.record)
        for update in [{"checker": {"resolved": False}}, {"exit_code": 75},
                       {"session_integrity": {"passed": False}}, {"unknown_usage_requests": 1},
                       {"accounting_unsettled": True}, {"cleanup_unsettled": True},
                       {"infrastructure_error": "grader failed"}, {"admission_refused": "cap"},
                       {"checker": {"resolved": True, "additional_proof_integrity": False}}]:
            with self.subTest(update=update):
                self.record = {**original, **update}
                self.save()
                self.assertFalse(review.qualify(self.run, self.approved())["qualified_success"])

    def test_restart_review_requires_actual_audit(self):
        self.record["requires_continuation_audit"] = True
        self.save()
        self.assertFalse(review.qualify(self.run, self.approved())["qualified_success"])
        self.record.update(sustained_gate_passed=True, continuation_audit={"status": "passed"})
        self.save()
        self.assertTrue(review.qualify(self.run, self.approved())["qualified_success"])

    def test_historical_results_are_ineligible(self):
        self.record["qualification_version"] = 2
        self.save()
        with self.assertRaisesRegex(ValueError, "older frozen result"):
            review.review_template(self.run)

    def test_new_request_evidence_gate_does_not_regrade_legacy_rows(self):
        self.assertNotIn("initial_task_request", review.automated_checks(self.record))
        self.record["request_evidence_version"] = 1
        self.save()
        self.assertFalse(review.qualify(self.run, self.approved())["qualified_success"])
        self.record["initial_task_request_evidence"] = {"passed": False, "reason": "changed integrity clause"}
        self.assertEqual(public.cohort_stop_reason(self.record), "initial task request evidence failed")
        self.record["initial_task_request_evidence"] = {"passed": True}
        self.save()
        self.assertTrue(review.qualify(self.run, self.approved())["qualified_success"])

    def test_pi_requires_unique_normal_terminal_and_known_tool_count(self):
        self.record.update(engine="pi", tool_dispatches=2)
        for event in [None, {"normalFinish": False, "stopReason": "stop"},
                      {"normalFinish": True, "stopReason": "length"}]:
            self.record["pi_terminal_observation"] = event
            self.save()
            self.assertFalse(review.qualify(self.run, self.approved())["qualified_success"])
        self.record["pi_terminal_observation"] = {"normalFinish": True, "stopReason": "stop", "error": None}
        self.save()
        self.assertTrue(review.qualify(self.run, self.approved())["qualified_success"])
        for update in [{"tool_dispatches": None}, {"tool_dispatches": True},
                       {"pi_terminal_observation_error": "missing or duplicate evaluation_end"}]:
            previous = copy.deepcopy(self.record)
            self.record.update(update)
            self.save()
            self.assertFalse(review.qualify(self.run, self.approved())["qualified_success"])
            self.record = previous

    def test_review_requires_complete_findings_and_rationale(self):
        for key, value in [("rationale", ""), ("reviewer", " "), ("checks", {}),
                           ("checks", dict.fromkeys(review.REVIEW_CHECKS, "yes"))]:
            item = self.approved()
            item[key] = value
            with self.assertRaises(ValueError):
                review.qualify(self.run, item)

    def test_cli_writes_separate_qualified_record_and_refuses_overwrite(self):
        source = self.run / "review.json"
        source.write_text(json.dumps(self.approved()))
        output = self.run / "qualified.json"
        args = [sys.executable, str(ROOT / "runner/patch_review.py"), "qualify", str(self.run),
                "--review", str(source), "--output", str(output)]
        subprocess.run(args, check=True, capture_output=True)
        self.assertTrue(json.loads(output.read_text())["qualified_success"])
        self.assertFalse(json.loads((self.run / "result.json").read_text())["success"])
        self.assertNotEqual(subprocess.run(args, capture_output=True).returncode, 0)

    def test_both_engine_prompts_receive_same_policy_without_lean_file_ban(self):
        broker = SimpleNamespace(records=[])
        args = SimpleNamespace(model="fixture", max_attempts=2, max_tools=2, context_bytes=30000, timeout=10,
            prepared_bwrap=None, harness_root=ROOT.parent, cohort="test", attempt=1, apt_https=False, apt_main_only=False)
        prompts = []
        for engine in ["lean", "pi"]:
            with patch.object(public, "harness_binary", return_value=self.run / "harness"), \
                 patch.object(public, "eval_tools_binary", return_value=self.run / "tools"), \
                 patch.object(public, "node_identity", return_value={"root": str(self.run), "binary": str(self.run / "bin/node"), "sha256": "fixture", "version": "v24.16.0"}), \
                 patch.object(public, "assert_space", side_effect=RuntimeError("stop before external work")):
                result = public.run_one({"id": "fixture", "benchmark": "SWE-fixture", "workspace": "/workspace",
                    "image_digest": "fixture"}, engine, 0, [], args, self.run, broker, task_text="Fix requested behavior.")
            output = self.run / result["run_id"]
            config = json.loads((output / "config.json").read_text())
            pi_config = json.loads((output / "pi-config.json").read_text())
            self.assertNotIn("Do not modify existing tests", config["instructions"])
            self.assertIn(review.TASK_CONSTRAINTS, pi_config["task"])
            self.assertEqual(result["qualification_version"], 3)
            self.assertEqual(result["qualification_status"], "pending_independent_review")
            prompts.append(pi_config["task"])
        self.assertEqual(prompts[0], prompts[1])

    def test_historical_aggregator_cannot_count_pending_reviews_as_failures(self):
        (self.run / "plan.json").write_text(json.dumps({"qualification_version": 3}))
        with self.assertRaisesRegex(ValueError, "cannot score v3 pending reviews"):
            summarize_public.summarize([self.run], include_unavailable=False)


if __name__ == "__main__":
    unittest.main()
