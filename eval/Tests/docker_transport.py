"""Offline endpoint-routing checks; no Docker daemon or network is required."""
import io
import json
import os
from pathlib import Path
import socket
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "runner"))
import docker_endpoint as transport
import public_bench as public
import resource_owner
import workspace_snapshot
import container_memory
import prepare_pilot
import paths


class DockerTransport(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.socket = socket.socket(socket.AF_UNIX)
        self.addCleanup(self.socket.close)
        self.path = Path(self.directory.name) / "docker.sock"
        self.socket.bind(str(self.path))
        self.host = "unix://" + str(self.path)

    def test_default_ignores_ambient_transport_and_secrets(self):
        with patch.dict(os.environ, {"DOCKER_HOST": "tcp://bad:2375", "DOCKER_CONTEXT": "bad",
                                     "ANTHROPIC_API_KEY": "not-a-real-key", "PYTHONPATH": "bad"}, clear=True):
            self.assertIsNone(transport.docker_host())
            self.assertEqual(set(transport.command_environment()), {"PATH", "HOME", "LANG"})

    def test_only_existing_absolute_unix_socket_is_accepted(self):
        regular = Path(self.directory.name) / "ordinary"
        regular.write_text("not a socket")
        invalid = ["", "tcp://127.0.0.1:2375", "ssh://host", "unix://relative", "unix:///missing",
                   "unix://" + str(regular), self.host + "?query", self.host + "\n",
                   self.host.replace("docker.sock", "../docker.sock")]
        for value in invalid:
            with self.subTest(value=value), patch.dict(os.environ, {"LEAN_HARNESS_DOCKER_HOST": value}):
                with self.assertRaises((ValueError, OSError)):
                    transport.command_environment()
        with patch.dict(os.environ, {"LEAN_HARNESS_DOCKER_HOST": self.host, "DOCKER_CONTEXT": "bad"}):
            env = transport.command_environment()
            self.assertEqual(env["DOCKER_HOST"], self.host)
            self.assertEqual(env["LEAN_HARNESS_DOCKER_HOST"], self.host)
            self.assertNotIn("DOCKER_CONTEXT", env)

    def test_public_sdk_and_cleanup_subprocesses_share_selected_endpoint(self):
        with patch.dict(os.environ, {"LEAN_HARNESS_DOCKER_HOST": self.host}), \
             patch.object(public.subprocess, "run", return_value=SimpleNamespace(returncode=0)) as run:
            public.docker("ps", "-aq")
            public.command(["python3", "-m", "swebench.harness.run_evaluation"])
            resource_owner.docker("ps", "-aq")
            self.assertEqual(run.call_count, 3)
            for call in run.call_args_list:
                self.assertEqual(call.kwargs["env"]["DOCKER_HOST"], self.host)

    def test_snapshot_memory_and_image_pinning_share_selected_endpoint(self):
        with patch.dict(os.environ, {"LEAN_HARNESS_DOCKER_HOST": self.host}):
            with patch.object(workspace_snapshot.subprocess, "check_output", return_value="false\n") as run:
                workspace_snapshot._require_stopped("candidate")
                self.assertEqual(run.call_args.kwargs["env"]["DOCKER_HOST"], self.host)
            child = SimpleNamespace(stdout=io.BytesIO(b""), wait=lambda **_: 0, poll=lambda: 0,
                                    kill=lambda: self.fail("already settled archive child killed"))
            with patch.object(workspace_snapshot.subprocess, "Popen", return_value=child) as popen:
                with workspace_snapshot._docker_stream("candidate", "/workspace"):
                    pass
                self.assertEqual(popen.call_args.kwargs["env"]["DOCKER_HOST"], self.host)
            with patch.object(container_memory.subprocess, "check_output", return_value="0\n") as run:
                self.assertIsNotNone(container_memory.ContainerMemory("candidate").start().error)
                self.assertEqual(run.call_args.kwargs["env"]["DOCKER_HOST"], self.host)
            with patch.object(prepare_pilot.subprocess, "check_output", return_value="[]") as run:
                with self.assertRaises(IndexError):
                    prepare_pilot.pin_image({"image": "fixture:tag"}, {})
                self.assertEqual(run.call_args.kwargs["env"]["DOCKER_HOST"], self.host)

    def test_invalid_override_dispatches_nothing(self):
        with patch.dict(os.environ, {"LEAN_HARNESS_DOCKER_HOST": "tcp://bad:2375"}), \
             patch.object(public.subprocess, "run") as run:
            with self.assertRaises(ValueError):
                public.docker("ps")
            run.assert_not_called()

    def test_cleanup_binds_daemon_and_never_falls_back(self):
        directory = Path(self.directory.name) / "owner"
        directory.mkdir()
        with patch.dict(os.environ, {"LEAN_HARNESS_DOCKER_HOST": self.host}):
            owner = resource_owner.Owner(directory)
            header = json.loads(owner.path.read_text().splitlines()[0])
            self.assertEqual(header["docker_endpoint"], self.host)
            with patch.object(resource_owner, "docker", return_value=SimpleNamespace(returncode=0, stdout="")):
                self.assertTrue(owner.cleanup()["settled"])
        with patch.dict(os.environ, {}, clear=True), patch.object(resource_owner, "docker") as run:
            report = resource_owner.cleanup_existing(directory)
            self.assertFalse(report["settled"])
            self.assertIn("different Docker endpoint", report["errors"][0])
            run.assert_not_called()

    def test_plan_provenance_records_explicit_endpoint(self):
        with patch.dict(os.environ, {"LEAN_HARNESS_DOCKER_HOST": self.host}):
            self.assertEqual(paths.evaluation_provenance()["docker_endpoint"], self.host)


if __name__ == "__main__":
    unittest.main()
