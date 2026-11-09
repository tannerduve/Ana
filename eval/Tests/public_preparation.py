"""Unpaid preparation checks: selection, authority boundaries and asset scope."""
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "runner"))
import prepare_pilot
import public_bench
import container_memory
from container_memory import ContainerMemory


class PublicPreparation(unittest.TestCase):
    @staticmethod
    def memory_fixture(directory, **events):
        directory = Path(directory)
        (directory / "memory.current").write_text("100")
        (directory / "memory.max").write_text("2147483648\n")
        values = {"low": 0, "high": 0, "max": 0, "oom": 0, "oom_kill": 0,
                  "oom_group_kill": 0, **events}
        (directory / "memory.events").write_text("".join(f"{key} {value}\n" for key, value in values.items()))
        return directory / "memory.current"

    def test_memory_samples_are_bounded_peaks_and_missing_is_not_zero(self):
        with tempfile.TemporaryDirectory() as directory:
            counter = Path(directory) / "memory.current"
            meter = ContainerMemory("fixture")
            meter.path = counter
            for value in [100, 200, 150]:
                counter.write_text(str(value))
                meter._sample()
            report = meter.stop()
            self.assertEqual((report["baseline_bytes"], report["sampled_peak_bytes"], report["samples"]), (100, 200, 3))
            counter.unlink()
            missing = ContainerMemory("fixture")
            missing.path = counter
            missing._sample()
            report = missing.stop()
            self.assertIsNone(report["sampled_peak_bytes"])
            self.assertTrue(report["unavailable_reason"])

    def test_memory_event_deltas_include_final_read_and_preserve_peak_semantics(self):
        with tempfile.TemporaryDirectory() as directory:
            meter = ContainerMemory("fixture")
            meter.path = self.memory_fixture(directory, oom=4, oom_kill=2, future_counter=7)
            meter._sample()
            meter.path.write_text("200")
            meter._sample()
            self.memory_fixture(directory, max=11, oom=7, oom_kill=3, future_counter=9)
            report = meter.stop()
            self.assertEqual((report["baseline_bytes"], report["sampled_peak_bytes"], report["samples"]), (100, 200, 2))
            diagnostic = report["cgroup_diagnostics"]
            events = diagnostic["memory_events"]
            self.assertEqual(events["before"]["value"]["oom"], 4)
            self.assertEqual(events["final"]["value"]["oom"], 7)
            self.assertEqual(events["last_observed"], events["final"])
            self.assertEqual(events["delta"], {"low": 0, "high": 0, "max": 11,
                                             "oom": 3, "oom_kill": 1, "oom_group_kill": 0,
                                             "future_counter": 2})
            self.assertIsNone(events["delta_unknown_reason"])
            self.assertLessEqual(events["before"]["observed_at_unix"], events["final"]["observed_at_unix"])
            self.assertEqual(diagnostic["memory_max"]["final"]["value"], 2147483648)
            self.assertIn("do not identify an OOM victim", diagnostic["interpretation"])

    def test_memory_start_and_stop_observe_same_discovered_cgroup(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cgroup = root / "candidate"
            cgroup.mkdir()
            self.memory_fixture(cgroup)
            (root / "proc-cgroup").write_text("0::/candidate\n")
            def fixture_path(value):
                return {"/sys/fs/cgroup": root, "/proc/123/cgroup": root / "proc-cgroup"}[value]
            with patch.object(container_memory.subprocess, "check_output", return_value="123\n") as inspect, \
                 patch.object(container_memory, "Path", side_effect=fixture_path):
                meter = ContainerMemory("fixture", interval_seconds=60).start()
                try:
                    self.memory_fixture(cgroup, oom=1)
                finally:
                    report = meter.stop()
            inspect.assert_called_once_with(["docker", "inspect", "--format", "{{.State.Pid}}", "fixture"],
                                            text=True, timeout=10, env=container_memory.command_environment())
            self.assertFalse(meter.thread.is_alive())
            self.assertEqual(report["samples"], 1)
            events = report["cgroup_diagnostics"]["memory_events"]
            self.assertEqual(events["delta"]["oom"], 1)
            self.assertGreaterEqual(events["before"]["elapsed_seconds"], 0)
            self.assertGreaterEqual(events["final"]["elapsed_seconds"], events["before"]["elapsed_seconds"])

    def test_memory_events_final_read_failure_retains_last_success_not_zero(self):
        with tempfile.TemporaryDirectory() as directory:
            meter = ContainerMemory("fixture")
            meter.path = self.memory_fixture(directory, oom_kill=3)
            meter._sample()
            (Path(directory) / "memory.events").unlink()
            report = meter.stop()
            events = report["cgroup_diagnostics"]["memory_events"]
            self.assertIsNone(events["final"]["value"])
            self.assertTrue(events["final"]["unknown_reason"])
            self.assertEqual(events["last_observed"]["value"]["oom_kill"], 3)
            self.assertIsNone(events["delta"])
            self.assertTrue(events["delta_unknown_reason"])
            self.assertIsNone(report["unavailable_reason"])

    def test_memory_events_invalid_or_missing_baseline_never_becomes_known_delta(self):
        valid = b"low 0\nhigh 0\nmax 0\noom 0\noom_kill 0\n"
        malformed = [None, b"", b"oom 0\n", valid + b"oom 1\n", valid.replace(b"low 0", b"low -1"),
                     valid.replace(b"low 0", b"low +1"), valid + b"extra 18446744073709551616\n",
                     valid + b"extra \xff\n", valid + b" " * 16385]
        for raw in malformed:
            with self.subTest(raw_length=None if raw is None else len(raw)), tempfile.TemporaryDirectory() as directory:
                meter = ContainerMemory("fixture")
                meter.path = self.memory_fixture(directory)
                path = Path(directory) / "memory.events"
                path.unlink() if raw is None else path.write_bytes(raw)
                meter._sample()
                # Diagnostic availability is separate from sampling/process/accounting policy.
                self.assertFalse(meter.stop_event.is_set())
                path.write_bytes(valid)
                events = meter.stop()["cgroup_diagnostics"]["memory_events"]
                self.assertIsNone(events["before"]["value"])
                self.assertEqual(events["final"]["value"]["oom_kill"], 0)
                self.assertIsNone(events["delta"])
                self.assertTrue(events["delta_unknown_reason"])

    def test_memory_events_decrease_or_key_change_cannot_hide_between_endpoints(self):
        for change in ("decrease", "keys"):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as directory:
                meter = ContainerMemory("fixture")
                meter.path = self.memory_fixture(directory, oom=7)
                meter._sample()
                self.memory_fixture(directory, oom=2 if change == "decrease" else 8,
                                    **({"future_counter": 1} if change == "keys" else {}))
                meter._sample()
                self.memory_fixture(directory, oom=12)
                events = meter.stop()["cgroup_diagnostics"]["memory_events"]
                self.assertEqual(events["before"]["value"]["oom"], 7)
                self.assertEqual(events["final"]["value"]["oom"], 12)
                self.assertIsNone(events["delta"])
                self.assertIn("decreased" if change == "decrease" else "fields changed", events["delta_unknown_reason"])

    def test_memory_limit_missing_invalid_and_unlimited_are_distinct(self):
        for raw in (None, b"", b"-1", b"unlimited", b"18446744073709551616", b"\xff"):
            with self.subTest(raw=raw), tempfile.TemporaryDirectory() as directory:
                meter = ContainerMemory("fixture")
                meter.path = self.memory_fixture(directory)
                meter._sample()
                path = Path(directory) / "memory.max"
                path.unlink() if raw is None else path.write_bytes(raw)
                limit = meter.stop()["cgroup_diagnostics"]["memory_max"]
                self.assertIsNone(limit["final"]["value"])
                self.assertTrue(limit["final"]["unknown_reason"])
                self.assertEqual(limit["last_observed"]["value"], 2147483648)
        with tempfile.TemporaryDirectory() as directory:
            meter = ContainerMemory("fixture")
            meter.path = self.memory_fixture(directory)
            meter._sample()
            (Path(directory) / "memory.max").write_text("max\n")
            limit = meter.stop()["cgroup_diagnostics"]["memory_max"]
            self.assertEqual(limit["before"]["value"], 2147483648)
            self.assertEqual(limit["final"]["value"], "max")
            self.assertIsNone(limit["final"]["unknown_reason"])

    def test_memory_final_observation_unknown_if_sampler_does_not_stop(self):
        with tempfile.TemporaryDirectory() as directory:
            meter = ContainerMemory("fixture")
            meter.path = self.memory_fixture(directory)
            meter._sample()
            joins = []
            meter.thread = SimpleNamespace(join=lambda **kwargs: joins.append(kwargs), is_alive=lambda: True)
            report = meter.stop()["cgroup_diagnostics"]
            self.assertEqual(joins, [{"timeout": 1}])
            self.assertIsNone(report["memory_events"]["delta"])
            for name in ("memory_events", "memory_max"):
                self.assertIsNone(report[name]["final"]["value"])
                self.assertIn("sampler did not stop", report[name]["final"]["unknown_reason"])

    def test_memory_no_start_has_explicit_unknown_diagnostics(self):
        report = ContainerMemory("fixture").stop()["cgroup_diagnostics"]
        for name in ("memory_events", "memory_max"):
            self.assertIsNone(report[name]["before"]["value"])
            self.assertTrue(report[name]["before"]["unknown_reason"])
            self.assertIsNone(report[name]["final"]["value"])
            self.assertTrue(report[name]["final"]["unknown_reason"])
        self.assertIsNone(report["memory_events"]["delta"])

    def test_fixed_selection_is_order_independent_and_solution_free(self):
        repos = prepare_pilot.DEVELOPMENT_REPOS + [f"repo{i}/library" for i in range(7)]
        rows = [{"repo": repo, "instance_id": f"{repo.replace('/', '__')}-{index}",
                 "base_commit": "a" * 40, "image": "official-image", "difficulty": "",
                 "patch": "DO-NOT-DISCLOSE-REFERENCE", "test_patch": "DO-NOT-DISCLOSE-TEST"}
                for repo in repos for index in range(6)]
        a, b = prepare_pilot.select(rows), prepare_pilot.select(list(reversed(rows)))
        self.assertEqual(a, b)
        dev, held = {x["id"] for x in a["development"]}, {x["id"] for x in a["heldout"]}
        self.assertEqual((len(dev), len(held), len(a["repeats"])), (4, 30, 6))
        self.assertFalse(dev & held)
        self.assertTrue(set(a["repeats"]) <= held)
        repositories = {row["repo"] for row in a["heldout"]}
        self.assertGreaterEqual(len(repositories), 8)
        self.assertTrue(all(sum(row["repo"] == repo for row in a["heldout"]) <= 4 for repo in repositories))
        self.assertNotIn("DO-NOT-DISCLOSE", json.dumps(a))
        self.assertIn("DRAFT", a["status"])

    def test_previously_seen_and_requests_are_never_heldout(self):
        repos = prepare_pilot.DEVELOPMENT_REPOS + [f"repo{i}/library" for i in range(7)]
        rows = [{"repo": repo, "instance_id": f"{repo.replace('/', '__')}-{index}",
                 "base_commit": "a", "image": "image", "difficulty": ""}
                for repo in repos for index in range(6)]
        rows += [{"repo": "psf/requests", "instance_id": name,
                  "base_commit": "a", "image": "image", "difficulty": ""}
                 for name in [*prepare_pilot.SEEN, "psf__requests-unseen"]]
        result = prepare_pilot.select(rows)
        excluded = {row["id"] for row in result["excluded"]}
        self.assertTrue(prepare_pilot.SEEN <= excluded)
        self.assertIn("psf__requests-unseen", excluded)
        self.assertFalse(excluded & {row["id"] for row in result["heldout"]})

    def test_prepared_binary_digest_and_privilege_mode(self):
        with tempfile.TemporaryDirectory() as directory:
            binary = Path(directory) / "bwrap"
            binary.write_bytes(b"fixture")
            binary.chmod(0o755)
            args = SimpleNamespace(prepared_bwrap=binary, bwrap_sha256=public_bench.sha(binary))
            self.assertEqual(public_bench.prepared_sandbox(args)["profile"], "bubblewrap")
            args.bwrap_sha256 = "0" * 64
            with self.assertRaisesRegex(RuntimeError, "differs"):
                public_bench.prepared_sandbox(args)
            args.bwrap_sha256 = public_bench.sha(binary)
            binary.chmod(0o4755)
            with self.assertRaisesRegex(RuntimeError, "non-setuid"):
                public_bench.prepared_sandbox(args)

    def test_swe_only_selection_never_reads_terminal_checkout_or_other_image(self):
        task = {"id": "selected", "benchmark": "SWE-bench Lite", "base_commit": "base",
                "image_digest": "official@sha256:digest", "image_id": "image-id",
                **{name + "_sha256": hashlib.sha256(name.encode()).hexdigest() for name in ["eval_script", "test_patch"]}}
        lock = {"terminal_bench": {"tasks": [{"id": "other", "benchmark": "terminal-bench"}]},
                "swebench": {"tasks": [task], "evaluator_version": "pinned", "evaluator_files_sha256": {"file": "hash"}}}
        calls = []
        def command(args, **kwargs):
            calls.append(args)
            return SimpleNamespace(stdout='pinned\n' if "print(swebench.__version__)" in args[2] else '{"file":"hash"}')
        def docker(*args, **kwargs):
            self.assertEqual(args, ("image", "inspect", task["image_digest"]))
            return SimpleNamespace(stdout='[{"Id":"image-id"}]')
        with tempfile.TemporaryDirectory() as directory:
            dataset = Path(directory) / "rows.json"
            dataset.write_text(json.dumps([{"instance_id": "selected", "base_commit": "base",
                                            "eval_script": "eval_script", "test_patch": "test_patch"}]))
            with patch.object(public_bench, "command", command), patch.object(public_bench, "docker", docker):
                rows = public_bench.check_assets(lock, Path("absent"), dataset, Path("python"), ["selected"])
            self.assertEqual(rows[0]["image"], task["image_digest"])
            self.assertEqual(len(calls), 2)
            with self.assertRaisesRegex(RuntimeError, "absent from the lock"):
                public_bench.check_assets(lock, Path("absent"), dataset, Path("python"), ["missing"])


if __name__ == "__main__":
    unittest.main()
