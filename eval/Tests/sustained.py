"""Offline restart, accounting-cleanup and manifest checks; no model calls."""
import json
import hashlib
from pathlib import Path
import sys
import tempfile
import threading
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "runner"))
import public_bench as public
import sustained
from continuation_audit import fixture as continuation_fixture


class UnsettledBroker:
    """An admitted request with a retained, genuinely unsettled reservation."""
    def __init__(self):
        self.records = []
        self.lock = threading.Lock()
        self.storage_failure = None

    def add_run(self, run_id, *args):
        self.records.append({"run_id": run_id, "attempt": 1, "charged_usd": 0.01,
                             "usage": None, "accounting_settled": False})
        return "http://127.0.0.1/fixture/v1/messages"


class Sustained(unittest.TestCase):
    def test_missing_first_task_evidence_does_not_mask_cleanup_or_budget_stop(self):
        evidence = {"initial_task_request_evidence": {"passed": False}, "success": False}
        self.assertEqual(public.cohort_stop_reason(evidence), "initial task request evidence failed")
        self.assertEqual(public.cohort_stop_reason({**evidence, "admission_refused": {"kind": "shared_campaign"}}),
                         "spending admission refused")
        self.assertEqual(public.cohort_stop_reason({**evidence, "admission_refused": True, "cleanup_unsettled": True}),
                         "candidate cleanup did not settle")
        self.assertFalse(evidence["initial_task_request_evidence"]["passed"])

    def test_restart_audit_uses_persisted_prices_and_charges(self):
        with tempfile.TemporaryDirectory() as temporary:
            cohort = Path(temporary)
            run = cohort / "continuation"
            run.mkdir()
            ledger, plan, _ = continuation_fixture(run, schema=3)
            (cohort / "broker.json").write_text(json.dumps(ledger))
            self.assertEqual(sustained.audit_restart(run, plan)["status"], "passed")
            ledger["prices_per_million"]["output"] = 40
            (cohort / "broker.json").write_text(json.dumps(ledger))
            with self.assertRaisesRegex(sustained.AuditError, "request cost differs"):
                sustained.audit_restart(run, plan)

    def test_pi_terminal_counter_missing_is_unknown(self):
        with tempfile.TemporaryDirectory() as directory:
            events = Path(directory) / "events.log"
            for rows, expected in [([], None), ([{"type": "evaluation_end", "toolDispatches": 0}], 0),
                                   ([{"type": "evaluation_end", "toolDispatches": 4}], 4),
                                   ([{"type": "evaluation_end", "toolDispatches": True}], None),
                                   ([{"type": "evaluation_end", "toolDispatches": 4}] * 2, None)]:
                events.write_text("".join(json.dumps(row) + "\n" for row in rows))
                self.assertEqual(public.pi_terminal_observation(events)["tool_dispatches"], expected)

    def test_manifest_rejects_changed_checker_task_and_image(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory) / "fixture"
            fixture.write_text("trusted artifact")
            record = {"path": str(fixture), "sha256": hashlib.sha256(fixture.read_bytes()).hexdigest()}
            task = {"id": "fixture", "task_text": "task",
                    "task_sha256": hashlib.sha256(b"task").hexdigest(),
                    "image_digest": "fixture@sha256:" + "a" * 64,
                    "reference_patch": record,
                    "checker": {"files": [{**record, "name": "check.py"}], "expected_counts": {"cases": 1}}}
            manifest = {"schema_version": 1, "tasks": [task], "modes": [{"id": "fixture", "engine": "lean",
                "max_attempts": 40, "max_tools": 120, "context_bytes": 60000, "timeout": 900, "yield_after": 12}]}
            sustained.validate_manifest(manifest)
            mode = manifest["modes"][0]
            for limit in [1, 4096, 8192]:
                mode["config"] = {"maxOutputTokens": limit}
                sustained.validate_manifest(manifest)
            for invalid in [True, False, "8192", 8192.0, None, 0, -1, 8193]:
                mode["config"] = {"maxOutputTokens": invalid}
                with self.subTest(output=invalid), self.assertRaises(ValueError):
                    sustained.validate_manifest(manifest)
            del mode["config"]
            for field, changed in [("task_text", "new task"), ("image_digest", "fixture:latest")]:
                prior = task[field]
                task[field] = changed
                with self.assertRaises(ValueError): sustained.validate_manifest(manifest)
                task[field] = prior
            fixture.write_text("changed checker")
            with self.assertRaisesRegex(ValueError, "missing or changed"):
                sustained.validate_manifest(manifest)

    def fixture_docker(self, codes, mismatch=False):
        invocations = []
        def docker(*args, **kwargs):
            if "inspect" in args or "replay" in args:
                state = {"nextId": len(invocations) * 12, "modelAttempts": len(invocations),
                         "toolDispatches": len(invocations), "phase": "control", "summaries": []}
                value = {"state": state, "pending": None, "terminal": False}
                if mismatch and "replay" in args:
                    state["nextId"] += 1
                return SimpleNamespace(stdout=json.dumps(value), returncode=0)
            invocations.append((args, kwargs["timeout"]))
            Path(kwargs["output"]).write_text(json.dumps({"invocation": len(invocations)}) + "\n")
            return SimpleNamespace(returncode=codes[len(invocations) - 1])
        return docker, invocations

    def fixture_command(self, docker):
        return lambda args, **kwargs: docker(*args, **kwargs)

    def test_restarts_append_events_and_preserve_each_checkpoint(self):
        docker, calls = self.fixture_docker([75, 75, 0])
        with tempfile.TemporaryDirectory() as directory, patch.object(public, "docker", docker), \
             patch.object(public, "command", self.fixture_command(docker)), \
             patch.object(public, "read_regular_file", return_value=b"fixture-journal"):
            output = Path(directory)
            result = public.run_invocations("container", ["exec", "run"], ["exec", "resume"], output, 30,
                                            yield_after=12, host_harness=Path("/fixture"))
            self.assertEqual(result["exit_code"], 0)
            self.assertEqual(len(result["durable_checkpoints"]), 2)
            self.assertEqual([row["exit_code"] for row in result["invocations"]], [75, 75, 0])
            self.assertEqual(len((output / "events.log").read_text().splitlines()), 3)
            self.assertEqual(calls[0][0], ("exec", "run", "--yield-after", "12"))
            self.assertEqual(calls[1][0], ("exec", "resume", "--yield-after", "12"))
            self.assertTrue(all(later[1] <= earlier[1] for earlier, later in zip(calls, calls[1:])))

    def test_schema7_checkpoint_preserves_actual_turn_and_refuses_missing_or_invalid(self):
        missing = object()
        for turn in [2, missing, True, -1]:
            with self.subTest(turn=turn), tempfile.TemporaryDirectory() as directory:
                docker, calls = self.fixture_docker([75, 0])
                def inspect(args, **kwargs):
                    value = json.loads(self.fixture_command(docker)(args, **kwargs).stdout)
                    value["state"]["schemaVersion"] = 7
                    if turn is not missing:
                        value["state"]["turn"] = turn
                    return SimpleNamespace(stdout=json.dumps(value), returncode=0)
                with patch.object(public, "docker", docker), patch.object(public, "command", inspect), \
                     patch.object(public, "read_regular_file", return_value=b"fixture-journal"):
                    arguments = ("container", ["exec", "run"], ["exec", "resume"], Path(directory), 30)
                    if type(turn) is int and turn >= 0:
                        result = public.run_invocations(*arguments, yield_after=12, host_harness=Path("/fixture"))
                        self.assertEqual(result["durable_checkpoints"][0]["turn"], turn)
                        self.assertEqual(len(calls), 2)
                    else:
                        with self.assertRaisesRegex(RuntimeError, "turn identity"):
                            public.run_invocations(*arguments, yield_after=12, host_harness=Path("/fixture"))
                        self.assertEqual(len(calls), 1)

    def test_mismatched_checkpoint_never_resumes(self):
        docker, calls = self.fixture_docker([75], mismatch=True)
        with tempfile.TemporaryDirectory() as directory, patch.object(public, "docker", docker), \
             patch.object(public, "command", self.fixture_command(docker)), \
             patch.object(public, "read_regular_file", return_value=b"fixture-journal"):
            with self.assertRaisesRegex(RuntimeError, "checkpoint replay"):
                public.run_invocations("container", ["exec", "run"], ["exec", "resume"], Path(directory), 30,
                                       yield_after=12, host_harness=Path("/fixture"))
            self.assertEqual(len(calls), 1)

    def test_restart_count_is_bounded(self):
        docker, calls = self.fixture_docker([75, 75])
        with tempfile.TemporaryDirectory() as directory, patch.object(public, "docker", docker), \
             patch.object(public, "command", self.fixture_command(docker)), \
             patch.object(public, "read_regular_file", return_value=b"fixture-journal"):
            with self.assertRaisesRegex(RuntimeError, "invocation ceiling"):
                public.run_invocations("container", ["exec", "run"], ["exec", "resume"], Path(directory), 30,
                                       yield_after=12, max_invocations=2, host_harness=Path("/fixture"))
            self.assertEqual(len(calls), 2)

    def test_accounting_failure_still_removes_container_and_records_attempt(self):
        class Broker(UnsettledBroker):
            def close_run(self, *args):
                calls.append("close")
                raise TimeoutError("fixture accounting timeout")
            def admission_refusal(self, *args): return None
        calls = []
        def docker(*args, **kwargs):
            if args[0] == "stop": calls.append("stop")
            return SimpleNamespace(returncode=0, stdout="")
        args = SimpleNamespace(model="fixture", max_attempts=2, max_tools=2, context_bytes=30000, timeout=10,
            prepared_bwrap=None, harness_root=ROOT.parent, cohort="test", attempt=1, apt_https=False, apt_main_only=False)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.object(public, "harness_binary", return_value=root / "harness"), \
                 patch.object(public, "eval_tools_binary", return_value=root / "tools"), \
                 patch.object(public, "node_identity", return_value={"root": str(root), "binary": str(root / "bin/node"), "sha256": "fixture", "version": "v24.16.0"}), \
                 patch.object(public, "validate_node_preflight", return_value={"status": "ok"}), \
                 patch.object(public, "create_container", return_value="fixture-container"), \
                 patch.object(public, "capture_baseline", return_value={"baseline_tree": "fixture-tree"}), \
                 patch.object(public, "assert_space"), \
                 patch.object(public, "docker", side_effect=docker), \
                 patch.object(public, "remove_container") as removed, \
                 patch.object(public, "run_invocations", side_effect=RuntimeError("checkpoint mirror failed")), \
                 patch.object(public, "capture_stopped_evidence"), \
                 patch.object(public, "ContainerMemory") as memory:
                memory.return_value.start.return_value.stop.return_value = {"unavailable_reason": "fixture"}
                result = public.run_one({"id": "fixture", "benchmark": "SWE-fixture", "workspace": "/workspace",
                    "image_digest": "fixture"}, "pi", 0, [], args, root, Broker(), task_text="task")
                self.assertTrue(result["accounting_unsettled"])
                self.assertFalse(result["success"])
                self.assertLess(calls.index("stop"), calls.index("close"))
                removed.assert_called_once_with("fixture-container")
                self.assertTrue((root / result["run_id"] / "result.json").is_file())

    def test_resolved_output_limit_reaches_configs_registration_and_result(self):
        from unittest.mock import Mock
        from contextlib import ExitStack
        for engine in ["lean", "pi"]:
            for options, expected in [({}, 4096), ({"max_output_tokens": 8192}, 8192),
                    ({"max_output_tokens": 512, "config_overrides": {"maxOutputTokens": 8192}}, 8192)]:
                with self.subTest(engine=engine, options=options), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory)
                    broker = Mock(records=[], lock=threading.Lock(), storage_failure=None)
                    broker.add_run.return_value = "http://127.0.0.1/fixture/v1/messages"
                    broker.admission_refusal.return_value = None
                    args = SimpleNamespace(model="fixture", max_attempts=2, max_tools=2, context_bytes=30000,
                        timeout=10, prepared_bwrap=None, harness_root=ROOT.parent, cohort="test", attempt=1,
                        apt_https=False, apt_main_only=False, **options)
                    with ExitStack() as stack:
                        for name, value in [("harness_binary", root / "harness"), ("eval_tools_binary", root / "tools"),
                                ("node_identity", {"root": str(root)}), ("validate_node_preflight", {"status": "ok"}),
                                ("create_container", "fixture-container"),
                                ("capture_baseline", {"baseline_tree": "fixture-tree"}),
                                ("assert_space", None), ("docker", SimpleNamespace(returncode=0, stdout="")),
                                ("capture_stopped_evidence", None)]:
                            stack.enter_context(patch.object(public, name, return_value=value))
                        removed = stack.enter_context(patch.object(public, "remove_container"))
                        stack.enter_context(patch.object(public, "run_invocations",
                            side_effect=RuntimeError("fixture stops after registration")))
                        memory = stack.enter_context(patch.object(public, "ContainerMemory"))
                        memory.return_value.start.return_value.stop.return_value = {"unavailable_reason": "fixture"}
                        record = public.run_one({"id": "fixture", "benchmark": "SWE-fixture", "workspace": "/workspace",
                            "image_digest": "fixture"}, engine, 0, [], args, root, broker, task_text="task")
                    broker.add_run.assert_called_once_with(record["run_id"], 2, 54000, expected)
                    for filename in ["config.json", "pi-config.json"]:
                        self.assertEqual(json.loads((root / record["run_id"] / filename).read_text())["maxOutputTokens"], expected)
                    self.assertEqual(record["max_output_tokens"], expected)
                    self.assertEqual(json.loads((root / record["run_id"] / "result.json").read_text())["max_output_tokens"], expected)
                    self.assertFalse(record["normal_finish"])
                    removed.assert_called_once_with("fixture-container")

    def test_pi_startup_failure_never_registers_or_dispatches_paid_work(self):
        from unittest.mock import Mock
        broker = Mock(records=[])
        args = SimpleNamespace(model="fixture", max_attempts=2, max_tools=2, context_bytes=30000, timeout=10,
            prepared_bwrap=None, harness_root=ROOT.parent, cohort="test", attempt=1, apt_https=False, apt_main_only=False)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.object(public, "harness_binary", return_value=root / "harness"), \
                 patch.object(public, "eval_tools_binary", return_value=root / "tools"), \
                 patch.object(public, "node_identity", return_value={"root": str(root), "binary": str(root / "bin/node"), "sha256": "fixture", "version": "v24.16.0"}), \
                 patch.object(public, "create_container", return_value="fixture-container"), \
                 patch.object(public, "capture_baseline", return_value={"baseline_tree": "fixture-tree"}), \
                 patch.object(public, "assert_space"), \
                 patch.object(public, "docker", return_value=SimpleNamespace(returncode=0, stdout="invalid startup marker")), \
                 patch.object(public, "capture_stopped_evidence"), \
                 patch.object(public, "remove_container") as removed, \
                 patch.object(public, "run_invocations") as run, \
                 patch.object(public, "swe_verify") as grade:
                result = public.run_one({"id": "fixture", "benchmark": "SWE-fixture", "workspace": "/workspace",
                    "image_digest": "fixture"}, "pi", 0, [], args, root, broker, task_text="task")
            broker.add_run.assert_not_called()
            run.assert_not_called()
            grade.assert_not_called()
            removed.assert_called_once_with("fixture-container")
            self.assertIn("Pi startup preflight", result["infrastructure_error"])
            self.assertTrue(result["runtime_prerequisite_failed"])
            self.assertEqual(result["provider_attempts"], 0)
            self.assertFalse(result["normal_finish"])

    def test_runtime_prerequisite_failure_preserves_unrun_schedule(self):
        from contextlib import ExitStack
        from unittest.mock import MagicMock
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            manifest_file, binary, key = root / 'manifest.json', root / 'binary', root / 'offline-key'
            manifest_file.write_text('{}'); binary.write_bytes(b'fixture'); key.write_text('offline-only')
            manifest = {'status': 'FROZEN_SUSTAINED', 'tasks': [{'id': task, 'image_digest': 'fixture', 'task_text': 'fixture task'} for task in ['first', 'second']],
                'modes': [{'id': engine, 'engine': engine, 'max_attempts': 2, 'max_tools': 2, 'context_bytes': 30000, 'timeout': 10}
                          for engine in ['pi', 'lean']]}
            broker = MagicMock()
            run = MagicMock(return_value={'task_id': 'first', 'mode': 'pi', 'engine': 'pi',
                'runtime_prerequisite_failed': True, 'infrastructure_error': 'startup failed', 'provider_attempts': 0})
            argv = ['sustained', 'run', '--manifest', str(manifest_file), '--output', str(root / 'output'),
                    '--prepared-bwrap', str(binary), '--bwrap-sha256', 'fixture', '--key-file', str(key),
                    '--campaign-dir', str(root / 'ledger')]
            with ExitStack() as stack:
                for owner, name, value in [(sustained, 'validate_manifest', manifest), (public, 'prepared_sandbox', None),
                    (public, 'docker', SimpleNamespace(returncode=0)), (sustained, 'harness_root', root),
                    (sustained, 'require_fresh_harness', binary), (sustained, 'harness_binary', binary),
                    (sustained, 'eval_tools_binary', binary), (sustained, 'node_root', root),
                    (sustained, 'product_provenance', {}), (sustained, 'evaluation_provenance', {})]:
                    stack.enter_context(patch.object(owner, name, return_value=value))
                stack.enter_context(patch.object(sustained.subprocess, 'check_output', return_value=b'[]'))
                factory = stack.enter_context(patch.object(sustained, 'Broker'))
                factory.return_value.__enter__.return_value = broker
                stack.enter_context(patch.object(public, 'run_one', run))
                stack.enter_context(patch.object(sys, 'argv', argv))
                self.assertEqual(sustained.main(), 2)
            run.assert_called_once()
            broker.add_run.assert_not_called()
            rows = json.loads((root / 'output/results.json').read_text())
            self.assertEqual(len(rows), 4)
            self.assertTrue(rows[0]['runtime_prerequisite_failed'])
            self.assertTrue(all(row['not_run'] and row['provider_attempts'] == 0 for row in rows[1:]))

    def test_unsettled_accounting_keeps_stopped_session_and_patch(self):
        calls = []
        class Broker(UnsettledBroker):
            def close_run(self, *args):
                calls.append("close")
                raise RuntimeError("unknown usage; reservation retained")
            def admission_refusal(self, *args): return None

        def mirror(container, source, target):
            self.assertIn("stop", calls)
            target.mkdir()
            (target / "journal.jsonl").write_text("retained session")
            return {"passed": True}

        def capture(container, workspace, target, baseline):
            self.assertIn("stop", calls)
            target.mkdir()
            patch_file = target / "patch"
            patch_file.write_text("retained patch")
            return {"patch_path": str(patch_file), "changed_paths": [], "existing_changed_paths": []}

        def docker(*args, **kwargs):
            if args[0] == "stop": calls.append("stop")
            return SimpleNamespace(returncode=0, stdout="")

        args = SimpleNamespace(model="fixture", max_attempts=2, max_tools=2, context_bytes=30000, timeout=10,
            prepared_bwrap=None, harness_root=ROOT.parent, cohort="test", attempt=1, apt_https=False, apt_main_only=False)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.object(public, "harness_binary", return_value=root / "harness"), \
                 patch.object(public, "eval_tools_binary", return_value=root / "tools"), \
                 patch.object(public, "node_identity", return_value={"root": str(root), "binary": str(root / "bin/node"), "sha256": "fixture", "version": "v24.16.0"}), \
                 patch.object(public, "validate_node_preflight", return_value={"status": "ok"}), \
                 patch.object(public, "create_container", return_value="fixture-container"), \
                 patch.object(public, "capture_baseline", return_value={"baseline_tree": "fixture-tree"}), \
                 patch.object(public, "assert_space"), patch.object(public, "docker", side_effect=docker), \
                 patch.object(public, "remove_container") as removed, \
                 patch.object(public, "run_invocations", return_value={"exit_code": 0}), \
                 patch.object(public, "mirror_session_after_stop", side_effect=mirror), \
                 patch.object(public, "capture_candidate_after_stop", side_effect=capture), \
                 patch.object(public, "ContainerMemory") as memory:
                memory.return_value.start.return_value.stop.return_value = {"unavailable_reason": "fixture"}
                result = public.run_one({"id": "fixture", "benchmark": "SWE-fixture", "workspace": "/workspace",
                    "image_digest": "fixture"}, "pi", 0, [], args, root, Broker(), task_text="task",
                    verify_patch=lambda *args: {"resolved": True})
                self.assertTrue(result["accounting_unsettled"])
                self.assertTrue(result["artifact_pass"])
                self.assertFalse(result["success"])
                output = root / result["run_id"]
                self.assertEqual((output / "sessions/journal.jsonl").read_text(), "retained session")
                self.assertEqual((output / "candidate.patch").read_text(), "retained patch")
                removed.assert_called_once_with("fixture-container")

    def test_unsettled_cleanup_is_reported_when_stop_and_removal_fail(self):
        class Broker(UnsettledBroker):
            def close_run(self, *args):
                calls.append("close")
                raise TimeoutError("fixture accounting timeout")
            def admission_refusal(self, *args): return None
        calls = []
        def docker(*args, **kwargs):
            if args[0] == "stop":
                calls.append("stop")
                raise RuntimeError("injected stop failure")
            if args[0] == "rm":
                calls.append("remove")
                raise RuntimeError("injected forced-removal failure")
            return SimpleNamespace(returncode=0, stdout="")
        args = SimpleNamespace(model="fixture", max_attempts=2, max_tools=2, context_bytes=30000, timeout=10,
            prepared_bwrap=None, harness_root=ROOT.parent, cohort="test", attempt=1, apt_https=False, apt_main_only=False)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.object(public, "harness_binary", return_value=root / "harness"), \
                 patch.object(public, "eval_tools_binary", return_value=root / "tools"), \
                 patch.object(public, "node_identity", return_value={"root": str(root), "binary": str(root / "bin/node"), "sha256": "fixture", "version": "v24.16.0"}), \
                 patch.object(public, "validate_node_preflight", return_value={"status": "ok"}), \
                 patch.object(public, "create_container", return_value="fixture-container"), \
                 patch.object(public, "capture_baseline", return_value={"baseline_tree": "fixture-tree"}), \
                 patch.object(public, "assert_space"), \
                 patch.object(public, "docker", side_effect=docker), \
                 patch.object(public, "remove_container", side_effect=RuntimeError("injected removal failure")) as removed, \
                 patch.object(public, "run_invocations", side_effect=RuntimeError("checkpoint mirror failed")), \
                 patch.object(public, "ContainerMemory") as memory:
                memory.return_value.start.return_value.stop.return_value = {"unavailable_reason": "fixture"}
                result = public.run_one({"id": "fixture", "benchmark": "SWE-fixture", "workspace": "/workspace",
                    "image_digest": "fixture"}, "pi", 0, [], args, root, Broker(), task_text="task")
                self.assertTrue(result["accounting_unsettled"])
                self.assertFalse(result["success"])
                self.assertTrue(result["cleanup_unsettled"])
                self.assertLess(calls.index("remove"), calls.index("close"))
                self.assertLess(calls.index("stop"), calls.index("close"))
                removed.assert_called_once_with("fixture-container")
                self.assertTrue((root / result["run_id"] / "result.json").is_file())

    def test_close_failure_classifies_only_matching_unsettled_records(self):
        marker = {"error": "OSError", "detail": "evidence flush failed", "at_unix": 1}
        for storage in (None, marker):
            for rows, expected in [([], False),
                    ([{"run_id": "other", "accounting_settled": False}], False),
                    ([{"run_id": "run", "accounting_settled": True}], False),
                    ([{"run_id": "run", "accounting_settled": False}], True),
                    ([{"run_id": "run"}], True)]:
                with self.subTest(storage=storage, rows=rows):
                    broker = SimpleNamespace(lock=threading.Lock(), storage_failure=storage, records=rows)
                    record = {}
                    public.record_broker_close_failure(record, broker, "run", RuntimeError("close failed"))
                    self.assertEqual(record["accounting_unsettled"], expected)
                    self.assertEqual(record.get("broker_storage_failure"), storage)
                    self.assertIsNotNone(public.cohort_stop_reason(record))
                    if storage and expected:
                        self.assertIn("accounting also did not settle", record["infrastructure_error"])
                    elif not expected:
                        self.assertNotIn("accounting did not settle", record["infrastructure_error"])

    def test_storage_failure_retains_known_charge_and_evidence_then_stops_both_schedules(self):
        from contextlib import ExitStack
        marker = {"error": "OSError", "detail": "injected broker snapshot flush failure", "at_unix": 1}
        for runner, failure in ((public, "storage"), (sustained, "storage"), (public, "late_settlement")):
            with self.subTest(runner=runner.__name__, failure=failure), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                calls = []

                class Broker(UnsettledBroker):
                    def __enter__(self): return self
                    def __exit__(self, *args): pass
                    def add_run(self, run_id, *args):
                        endpoint = super().add_run(run_id, *args)
                        if failure == "storage":
                            self.records[-1].update(accounting_settled=True, charged_usd=0.125,
                                                    usage={"input_tokens": 5, "output_tokens": 2})
                        return endpoint
                    def close_run(self, *args):
                        calls.append("close")
                        if failure == "late_settlement":
                            if calls.count("close") == 1:
                                raise TimeoutError("first close timed out before accounting settled")
                            self.records[-1].update(accounting_settled=True, charged_usd=0.125,
                                                    usage={"input_tokens": 5, "output_tokens": 2})
                            return
                        self.storage_failure = dict(marker)
                        raise RuntimeError("broker evidence storage failed; durable campaign charges are retained")
                    def admission_refusal(self, *args): return None

                broker = Broker()
                binary, key, manifest_file = root / "binary", root / "key", root / "manifest.json"
                binary.write_bytes(b"fixture"); key.write_text("localhost-fixture-only")
                selected = [{"id": name, "benchmark": "SWE-fixture", "workspace": "/workspace",
                             "image_digest": "fixture", "task_text": "fixture task"} for name in ("first", "second")]
                manifest = {"status": "FROZEN_SUSTAINED", "tasks": selected, "modes": [
                    {"id": engine, "engine": engine, "max_attempts": 2, "max_tools": 2,
                     "context_bytes": 30000, "timeout": 10} for engine in ("pi", "lean")]}
                manifest_file.write_text(json.dumps({"swebench": {"tasks": selected}}))

                def docker(*args, **kwargs):
                    if args[0] == "stop": calls.append("stop")
                    return SimpleNamespace(returncode=0, stdout="")

                def mirror(container, source, target):
                    self.assertIn("stop", calls)
                    target.mkdir()
                    (target / "journal.jsonl").write_bytes(b"retained known-charge session\n")
                    return {"entries": 1}

                def capture(container, workspace, target, baseline):
                    self.assertIn("stop", calls)
                    target.mkdir()
                    saved = target / "patch"
                    saved.write_bytes(b"retained candidate patch\n")
                    return {"patch_path": str(saved), "changed_paths": ["source.py"], "existing_changed_paths": ["source.py"]}

                argv = [runner.__name__, "run", "--output", str(root / "output"),
                        "--key-file", str(key), "--campaign-dir", str(root / "ledger")]
                if runner is sustained:
                    argv += ["--manifest", str(manifest_file), "--prepared-bwrap", str(binary), "--bwrap-sha256", "fixture"]
                else:
                    argv += ["--lock", str(manifest_file), "--allocation", "heldout", "--engines", "pi", "lean"]
                with ExitStack() as stack:
                    for owner, name, value in [
                        (public, "harness_binary", binary), (public, "eval_tools_binary", binary),
                        (public, "harness_root", root), (public, "require_fresh_harness", binary),
                        (public, "node_root", root), (public, "node_identity", {"root": str(root)}),
                        (public, "validate_node_preflight", {"status": "ok"}),
                        (public, "prepared_sandbox", None), (public, "assert_space", None),
                        (public, "create_container", "owned-fixture-container"),
                        (public, "capture_baseline", {"baseline_tree": "fixture"}),
                        (public, "run_invocations", {"exit_code": 0}),
                        (public, "swe_verify", {"resolved": True}),
                        (public, "check_assets", [{"instance_id": task["id"], "problem_statement": task["task_text"]} for task in selected]),
                        (public, "product_provenance", {}), (public, "evaluation_provenance", {}),
                        (public, "Owner", SimpleNamespace(uncertain=False, cleanup=lambda: {"settled": True})),
                        (sustained, "validate_manifest", manifest), (sustained, "harness_root", root),
                        (sustained, "require_fresh_harness", binary), (sustained, "harness_binary", binary),
                        (sustained, "eval_tools_binary", binary), (sustained, "node_root", root),
                        (sustained, "product_provenance", {}), (sustained, "evaluation_provenance", {}),
                        (sustained, "verify_feature", {"resolved": True})]:
                        stack.enter_context(patch.object(owner, name, return_value=value))
                    stack.enter_context(patch.object(runner, "Broker", return_value=broker))
                    stack.enter_context(patch.object(public, "ACTIVE_OWNER", None))
                    stack.enter_context(patch.object(public, "docker", side_effect=docker))
                    stack.enter_context(patch.object(public, "mirror_session_after_stop", side_effect=mirror))
                    stack.enter_context(patch.object(public, "capture_candidate_after_stop", side_effect=capture))
                    removed = stack.enter_context(patch.object(public, "remove_container"))
                    memory = stack.enter_context(patch.object(public, "ContainerMemory"))
                    memory.return_value.start.return_value.stop.return_value = {"unavailable_reason": "fixture"}
                    stack.enter_context(patch.object(public.subprocess, "check_output", return_value=b"[]"))
                    stack.enter_context(patch.object(sys, "argv", argv))
                    self.assertEqual(runner.main(), 2)
                rows = json.loads((root / "output/results.json").read_text())
                self.assertEqual(len(rows), 4)
                first = rows[0]
                if failure == "storage":
                    self.assertEqual(first["broker_storage_failure"], marker)
                    reason = "broker evidence storage failed"
                else:
                    self.assertNotIn("broker_storage_failure", first)
                    self.assertNotIn("accounting did not settle", first["infrastructure_error"])
                    reason = "broker close failed"
                self.assertFalse(first["accounting_unsettled"])
                self.assertEqual(first["accounted_usd"], 0.125)
                self.assertEqual(first["unknown_usage_requests"], 0)
                self.assertEqual(first["provider_attempts"], 1)
                self.assertFalse(first["automated_qualification_checks"]["settled_execution"])
                self.assertEqual(len(broker.records), 1, "no second run may register after evidence storage fails")
                self.assertTrue(broker.records[0]["accounting_settled"])
                self.assertEqual(broker.records[0]["charged_usd"], 0.125)
                self.assertTrue(all(row["not_run"] and row["provider_attempts"] == 0 and
                                    row["unrun_reason"] == reason for row in rows[1:]))
                run = root / "output" / first["run_id"]
                self.assertEqual((run / "sessions/journal.jsonl").read_bytes(), b"retained known-charge session\n")
                self.assertEqual((run / "candidate.patch").read_bytes(), b"retained candidate patch\n")
                self.assertEqual(json.loads((run / "result.json").read_text()), first)
                removed.assert_called_once_with("owned-fixture-container")
                self.assertLess(calls.index("stop"), calls.index("close"))


if __name__ == "__main__":
    unittest.main()
