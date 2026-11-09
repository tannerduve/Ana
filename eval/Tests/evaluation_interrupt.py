"""Unpaid Docker lifecycle checks. Requires a cached Ubuntu image; never pulls.

The run_one fixture uses a real localhost Broker request and a real container,
then replaces only the agent invocation with a blocking command. It tests
interruption/cleanup, not model or sandbox quality. This is an explicit local
Docker gate, separate from the Docker-free evaluation unit suite.
"""
import hashlib
import http.server
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import threading
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import urllib.request
import uuid

ROOT = Path(os.environ.get("HARNESS_EVAL_ROOT", str(Path(__file__).resolve().parents[1])))
RUNNER = Path(os.environ.get("HARNESS_EVAL_RUNNER", str(ROOT / "runner")))
sys.path[:0] = [str(RUNNER), str(ROOT / "runner")]
import resource_owner
import public_bench as public
from broker import Broker

IMAGE = os.environ.get("HARNESS_INTERRUPT_IMAGE", "ubuntu:24.04")
BASELINE_BYTES = b"original fixture source\n"
EDITED_BYTES = b"retained interrupted edit\n"
SESSION_BYTES = b'{"fixture":"durable session before interruption"}\n'
ARTIFACT_BYTES = bytes([0, 1, 127, 128, 255])



def docker(*args, check=True):
    result = subprocess.run(["docker", *map(str, args)], capture_output=True, text=True, timeout=30,
                            env=public.command_environment())
    if check and result.returncode:
        raise RuntimeError("Docker fixture failed: " + result.stderr[-1000:])
    return result


def fixture_child(directory, forced):
    """Exercise actual run_one finally blocks and the ownership journal."""
    directory = Path(directory)
    public.ROOT = ROOT
    owner = resource_owner.Owner(directory)
    public.ACTIVE_OWNER = owner
    if forced:
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        signal.signal(signal.SIGTERM, signal.SIG_IGN)

    class Handler(http.server.BaseHTTPRequestHandler):
        def log_message(self, *args):
            pass

        def do_POST(self):
            self.rfile.read(int(self.headers["Content-Length"]))
            body = json.dumps({"content": [{"type": "text", "text": "fixture"}],
                               "stop_reason": "end_turn", "usage": {"input_tokens": 3, "output_tokens": 2}}).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

    server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    original_create, original_docker = public.create_container, public.docker

    def create(image, **_):
        name = original_create(image, workspace="/workspace", mounts=(), network="none")
        ident = docker("inspect", "--format", "{{.Id}}", name).stdout.strip()
        (directory / "candidate-id").write_text(ident)
        original_docker("exec", name, "/bin/sh", "-c",
                        "mkdir -p /workspace /sessions; printf 'original fixture source\\n' > /workspace/answer.txt")
        return name

    def prepared_docker(*args, **kwargs):
        # Skip repository/transport preparation, which is unrelated to the
        # interruption boundary and would require installing packages.
        if args[0] == "exec":
            return SimpleNamespace(returncode=0, stdout="")
        return original_docker(*args, **kwargs)

    def invocation(container, _invocation, _resume, output, _timeout, **_):
        endpoint = json.loads((output / "config.json").read_text())["testEndpoint"]
        raw = json.dumps({"model": "claude-opus-5-5", "max_tokens": 8,
                          "messages": [{"role": "user", "content": "synthetic request"}]}).encode()
        request = urllib.request.Request(endpoint, data=raw, headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(request, timeout=10) as response:
            assert response.status == 200
            response.read()
        deadline = time.monotonic() + 5
        while any(row.get("active") for row in broker.records):
            if time.monotonic() >= deadline:
                raise RuntimeError("synthetic request did not settle")
            time.sleep(.01)
        original_docker("exec", container, "/bin/sh", "-c",
            "printf 'retained interrupted edit\\n' > /workspace/answer.txt; "
            "printf '{\"fixture\":\"durable session before interruption\"}\\n' > /sessions/trace.jsonl; "
            "mkdir -p /sessions/artifacts; printf '\\000\\001\\177\\200\\377' > /sessions/artifacts/raw.bin")
        (directory / "ready").write_text("provider settled; candidate active")
        # A real Docker process remains active until run_one cleanup or explicit
        # owner recovery removes it. No Docker socket is mounted in the child.
        return original_docker("exec", container, "/bin/sh", "-c", "exec sleep 600", timeout=620)

    args = SimpleNamespace(model="claude-opus-5-5", max_attempts=2, max_tools=2,
        context_bytes=30000, timeout=600, prepared_bwrap=None, harness_root=ROOT.parent,
        cohort="unpaid-interruption", attempt=1, apt_https=False, apt_main_only=False)
    task = {"id": "interrupt-fixture", "benchmark": "self-authored lifecycle fixture",
            "repository_task": True, "workspace": "/workspace", "image_digest": IMAGE}
    try:
        with Broker("synthetic-offline-only", directory, budget=1,
                    upstream=f"http://127.0.0.1:{server.server_port}/v1/messages") as broker:
            with patch.object(public, "create_container", side_effect=create), \
                 patch.object(public, "docker", side_effect=prepared_docker), \
                 patch.object(public, "node_identity", return_value={"root": str(directory),
                     "binary": str(directory / "bin/node"), "sha256": "fixture", "version": "v22.19.0"}), \
                 patch.object(public, "validate_node_preflight", return_value={"status": "fixture"}), \
                 patch.object(public, "harness_binary", return_value=directory / "unused-harness"), \
                 patch.object(public, "eval_tools_binary", return_value=directory / "unused-tools"), \
                 patch.object(public, "run_invocations", side_effect=invocation):
                public.run_one(task, "pi", 0, [], args, directory, broker, task_text="Synthetic cleanup fixture")
    finally:
        server.shutdown()
        server.server_close()


class EvaluationInterruption(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Fail explicitly instead of silently skipping an isolation/lifecycle gate.
        inspected = docker("image", "inspect", IMAGE, check=False)
        if inspected.returncode:
            raise RuntimeError(f"cache the explicitly selected image {IMAGE} before this local Docker gate; this test never pulls")
        cls.image_id = json.loads(inspected.stdout)[0]["Id"]

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.directory = Path(self.temp.name)
        self.foreign = docker("run", "-d", "--network", "none", "--label", "fixture=unrelated",
                              self.image_id, "/bin/sh", "-c", "exec sleep 600").stdout.strip()
        self.owned = []

    def tearDown(self):
        # Also settle a fixture that failed before returning its container ID.
        # The random private header authorizes only this test's exact labels.
        if (self.directory / resource_owner.NAME).is_file():
            resource_owner.cleanup_existing(self.directory)
        # Every ID originates in this test's own docker create return value.
        for ident in self.owned + [self.foreign]:
            docker("rm", "-f", ident, check=False)
        self.temp.cleanup()

    def assert_foreign_active(self):
        self.assertEqual(docker("inspect", "--format", "{{.State.Running}}", self.foreign).stdout.strip(), "true")

    def test_lost_create_ack_recovers_only_exact_label(self):
        owner = resource_owner.Owner(self.directory)
        name = "harness-interrupt-test-" + uuid.uuid4().hex
        label = owner.intent(name, self.image_id)
        ident = docker("run", "-d", "--name", name, "--label", label, "--network", "none",
                       self.image_id, "/bin/sh", "-c", "exec sleep 600").stdout.strip()
        self.owned.append(ident)
        # Deliberately omit owner.created: daemon completed but acknowledgement
        # was lost before it reached the durable owner journal.
        report = resource_owner.cleanup_existing(self.directory)
        self.assertTrue(report["settled"], report)
        self.assertEqual(report["removed"], [ident])
        self.assertNotEqual(docker("inspect", ident, check=False).returncode, 0)
        repeated = resource_owner.cleanup_existing(self.directory)
        self.assertTrue(repeated["settled"], repeated)
        self.assertEqual(repeated["removed"], [])
        records = [json.loads(line) for line in owner.path.read_text().splitlines()]
        self.assertEqual(sum(row["kind"] == "observed" for row in records), 1)
        self.assert_foreign_active()

    def test_unacknowledged_create_with_empty_scan_is_uncertain(self):
        owner = resource_owner.Owner(self.directory)
        name = "harness-interrupt-unknown-" + uuid.uuid4().hex
        owner.intent(name, self.image_id)
        # The daemon may still be processing an interrupted request. Absence
        # now cannot establish that no container will appear later.
        report = resource_owner.cleanup_existing(self.directory)
        self.assertFalse(report["settled"], report)
        self.assertEqual(report["unresolved_intents"], [name])
        self.assertEqual(report["removed"], [])
        self.assert_foreign_active()

    def test_bad_header_and_discovery_failure_do_not_claim_cleanup(self):
        owner = resource_owner.Owner(self.directory)
        with patch.object(resource_owner, "docker", return_value=SimpleNamespace(returncode=1, stdout="")):
            report = owner.cleanup()
        self.assertFalse(report["settled"])
        self.assertTrue(report["errors"])
        for raw in [b'{"kind":"owner"', b'[]\n', b'null\n', b'"header"\n', b'7\n']:
            with self.subTest(header=raw):
                owner.path.write_bytes(raw)
                report = resource_owner.cleanup_existing(self.directory)
                self.assertFalse(report["settled"])
                self.assertEqual(report.get("removed", []), [])
        self.assert_foreign_active()

    def child(self, forced):
        env = dict(os.environ, HARNESS_EVAL_ROOT=str(ROOT), HARNESS_EVAL_RUNNER=str(RUNNER),
                   HARNESS_INTERRUPT_IMAGE=self.image_id)
        log = (self.directory / "child.log").open("w")
        child = subprocess.Popen([sys.executable, __file__, "--fixture-child", str(self.directory), str(int(forced))],
                                 stdout=log, stderr=subprocess.STDOUT, env=env, start_new_session=True)
        deadline = time.monotonic() + 25
        while not (self.directory / "ready").exists() and child.poll() is None and time.monotonic() < deadline:
            time.sleep(.05)
        if not (self.directory / "ready").exists():
            if child.poll() is None:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
            log.close()
            self.fail("fixture did not reach active candidate: " + (self.directory / "child.log").read_text()[-3000:])
        ident = (self.directory / "candidate-id").read_text()
        self.owned.append(ident)
        return child, log, ident

    def test_sigint_preserves_edited_workspace_session_and_settled_attempt(self):
        child, log, ident = self.child(False)
        try:
            child.send_signal(signal.SIGINT)
            child.wait(timeout=20)
            self.assertNotEqual(child.returncode, 0)
            self.assertNotEqual(docker("inspect", ident, check=False).returncode, 0)
            results = list(self.directory.glob("interrupt-fixture-pi-0-*/result.json"))
            self.assertEqual(len(results), 1)
            result = json.loads(results[0].read_text())
            self.assertFalse(result["success"])
            self.assertEqual(result["provider_attempts"], 1)
            self.assertFalse(result.get("accounting_unsettled", False))
            self.assertFalse(result.get("cleanup_unsettled", False))
            self.assertTrue(result["interrupted"])
            self.assertEqual(result["interruption"], "KeyboardInterrupt")
            self.assertNotIn("checker", result)  # No new grader after interruption.
            self.assertEqual(result["evidence_capture"]["session"]["status"], "captured")
            self.assertEqual(result["evidence_capture"]["workspace"]["status"], "captured")
            run = results[0].parent
            self.assertEqual((run / "sessions/trace.jsonl").read_bytes(), SESSION_BYTES)
            self.assertEqual((run / "sessions/artifacts/raw.bin").read_bytes(), ARTIFACT_BYTES)
            snapshot = result["workspace_snapshot"]
            self.assertEqual(snapshot["changed_paths"], ["answer.txt"])
            baseline = json.loads(Path(snapshot["baseline_manifest"]).read_text())
            candidate = json.loads(Path(snapshot["candidate_manifest"]).read_text())
            self.assertEqual(baseline["answer.txt"]["sha256"], hashlib.sha256(BASELINE_BYTES).hexdigest())
            self.assertEqual(candidate["answer.txt"]["sha256"], hashlib.sha256(EDITED_BYTES).hexdigest())
            patch_bytes = (run / "candidate.patch").read_bytes()
            self.assertIn(b"-original fixture source", patch_bytes)
            self.assertIn(b"+retained interrupted edit", patch_bytes)
            self.assertEqual(hashlib.sha256(patch_bytes).hexdigest(), result["candidate_patch_sha256"])
            charges = json.loads((self.directory / "broker.json").read_text())["records"]
            self.assertEqual(len(charges), 1)
            self.assertFalse(charges[0]["active"])
            self.assertIsNotNone(charges[0]["usage"])
            self.assert_foreign_active()
        finally:
            if child.poll() is None:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
            log.close()

    def test_forced_runner_death_requires_explicit_owner_recovery(self):
        child, log, ident = self.child(True)
        try:
            os.killpg(child.pid, signal.SIGINT)
            time.sleep(.2)
            self.assertIsNone(child.poll())
            os.killpg(child.pid, signal.SIGKILL)
            child.wait(timeout=10)
            self.assertEqual(docker("inspect", "--format", "{{.State.Running}}", ident).stdout.strip(), "true")
            self.assertEqual(list(self.directory.glob("interrupt-fixture-pi-0-*/result.json")), [])
            report = resource_owner.cleanup_existing(self.directory)
            self.assertTrue(report["settled"], report)
            self.assertEqual(report["removed"], [ident])
            self.assertNotEqual(docker("inspect", ident, check=False).returncode, 0)
            charges = json.loads((self.directory / "broker.json").read_text())["records"]
            self.assertEqual(len(charges), 1)
            self.assertFalse(charges[0]["active"])
            self.assert_foreign_active()
        finally:
            if child.poll() is None:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
            log.close()


if __name__ == "__main__":
    if len(sys.argv) == 4 and sys.argv[1] == "--fixture-child":
        fixture_child(sys.argv[2], bool(int(sys.argv[3])))
    else:
        unittest.main()
