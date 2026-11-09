#!/usr/bin/env python3
"""Regression checks for evaluation accounting, independent of model/API calls."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("public_report", ROOT / "runner/summarize_public.py")
report = importlib.util.module_from_spec(spec)
spec.loader.exec_module(report)


class Reporting(unittest.TestCase):
    def fixture(self, root, name, *, attempt=1, launched=True, resolved=False, cohort="original-preselection"):
        directory = root / name
        directory.mkdir()
        plan = {"public_lock_sha256": "lock", "binary_sha256": "binary", "tool_binary_sha256": "tool",
                "pi_lock_sha256": "pi", "model": "fixture", "max_attempts": 12, "max_tools": 24,
                "context_bytes": 120000, "timeout_seconds": 300,
                "tasks": ["prove-plus-comm"], "engines": ["lean"], "repetition_start": 1, "repetitions": 1}
        (directory / "plan.json").write_text(json.dumps(plan))
        prices = {"input": 4, "output": 20, "cache_read": .2, "cache_write": 5}
        ledger = {"prices_per_million": prices, "records": []}
        result = {"run_id": name, "task_id": "prove-plus-comm", "engine": "lean", "benchmark": "terminal-bench",
                  "track": "product", "repetition": 1, "attempt": attempt, "cohort": cohort, "success": resolved,
                  "provider_attempts": 0, "accounted_usd": 0, "unknown_usage_requests": 0,
                  "checker": {"resolved": resolved}}
        if launched:
            result["exit_code"] = 0
        else:
            result["infrastructure_error"] = "setup failed before launch"
        (directory / "broker.json").write_text(json.dumps(ledger))
        (directory / name).mkdir()
        (directory / name / "result.json").write_text(json.dumps(result))
        return directory

    def test_retry_preserves_setup_failure_and_logical_slot(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            failed = self.fixture(root, "failed", launched=False)
            retry = self.fixture(root, "retry", attempt=2, resolved=True)
            result = report.summarize([failed, retry])
            self.assertEqual(result["execution_attempt_records"], 2)
            self.assertEqual(result["executed_runs"], 1)
            self.assertEqual(result["setup_failures"], 1)
            self.assertEqual(result["additional_retry_attempts"], 1)
            self.assertEqual(result["total_planned_run_slots"], 3)  # one slot plus two unavailable Requests slots
            self.assertEqual(len(result["planned_unexecuted"]), 2)

    def test_diagnostic_is_separate_without_original_unavailable_slots(self):
        with tempfile.TemporaryDirectory() as tmp:
            run = self.fixture(Path(tmp), "diagnostic", resolved=True, cohort="flask-budget-diagnostic")
            result = report.summarize([run], include_unavailable=False)
            self.assertEqual(result["total_planned_run_slots"], 1)
            self.assertEqual(result["planned_unexecuted"], [])
            self.assertIn("excluded from the frozen comparison", report.diagnostic_markdown(result))

    def test_distinct_cohorts_are_not_retries(self):
        with tempfile.TemporaryDirectory() as tmp:
            first = self.fixture(Path(tmp), "first")
            diagnostic = self.fixture(Path(tmp), "diagnostic", cohort="flask-budget-diagnostic")
            result = report.summarize([first, diagnostic], include_unavailable=False)
            self.assertEqual(result["additional_retry_attempts"], 0)
            self.assertEqual(result["total_planned_run_slots"], 2)

    def test_incomplete_declared_batch_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = self.fixture(Path(tmp), "incomplete")
            path = directory / "plan.json"
            plan = json.loads(path.read_text())
            plan["repetitions"] = 2
            path.write_text(json.dumps(plan))
            with self.assertRaisesRegex(ValueError, "incomplete or unexpected declared batch"):
                report.summarize([directory], include_unavailable=False)

    def test_modes_reject_mixed_cohorts_in_both_directions(self):
        mixed = {"runs": [{"cohort": "original-preselection"}, {"cohort": "flask-budget-diagnostic"}]}
        for diagnostic in [True, False]:
            with self.assertRaises(ValueError):
                report.validate_mode(mixed, diagnostic)

    def test_explicit_preflight_unavailable_is_a_recorded_slot(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = self.fixture(Path(tmp), "completed")
            path = directory / "plan.json"
            plan = json.loads(path.read_text())
            plan["tasks"].append("unavailable")
            path.write_text(json.dumps(plan))
            (directory / "results.json").write_text(json.dumps([
                {"task_id": "unavailable", "engine": "lean", "repetition": 1, "not_run": True,
                 "provider_attempts": 0, "infrastructure_error": "preflight failed"}]))
            result = report.summarize([directory], include_unavailable=False)
            self.assertEqual(result["total_planned_run_slots"], 2)
            self.assertEqual(result["executed_runs"], 1)
            self.assertEqual(result["planned_unexecuted"][0]["task_id"], "unavailable")

    def test_exact_cache_cost_and_unknown_charge(self):
        from decimal import Decimal
        prices = {"input": 4, "output": 20, "cache_read": .2, "cache_write": 5}
        value = report.accounted({"usage": {"input_tokens": 1000, "output_tokens": 100,
                                  "cache_read_input_tokens": 2000, "cache_creation_input_tokens": 3000}}, prices)
        self.assertEqual(value, Decimal("0.0214"))
        self.assertEqual(report.accounted({"usage": None, "charged_usd": .6}, prices), Decimal("0.6"))


if __name__ == "__main__":
    unittest.main()
