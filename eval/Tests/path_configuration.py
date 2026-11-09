"""Offline checks for explicit product roots and stale proxy rejection."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "runner"))
import paths


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class PathConfiguration(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.product, self.evals = self.root / "product", self.root / "evaluations"
        (self.product / "Harness").mkdir(parents=True)
        (self.evals / "eval").mkdir(parents=True)
        for name, text in [("lean-toolchain", "leanprover/lean4:v4.33.1\n"),
                           ("rust-toolchain.toml", '[toolchain]\nchannel="1.97.1"\n')]:
            (self.product / name).write_text(text)
            (self.evals / name).write_text(text)
        (self.product / "Harness/Core.lean").write_text("def fixture := 1\n")
        (self.evals / "Tools.lean").write_text("-- fixture proxy\n")
        subprocess.run(["git", "init", "--quiet", self.product], check=True)
        self.proxy = self.evals / ".lake/build/bin/eval_tools"
        self.proxy.parent.mkdir(parents=True)
        self.proxy.write_text("#!/bin/sh\nexit 0\n")
        self.proxy.chmod(0o755)
        self.identity_path = self.proxy.with_name("eval_tools.identity.json")
        self.identity = {"schema_version": 1, "harness_root": str(self.product), "harness_commit": "fixture",
                         "harness_sources_sha256": paths.product_source_hashes(self.product),
                         "tool_binary_sha256": sha(self.proxy),
                         "tool_source_sha256": sha(self.evals / "Tools.lean")}
        self.identity_path.write_text(json.dumps(self.identity))
        self.scope = patch.object(paths, "EVAL_ROOT", self.evals)
        self.scope.start()
        self.addCleanup(self.scope.stop)

    def test_default_root_is_declared_parent_and_must_be_product(self):
        with patch.dict(os.environ, {}, clear=True), self.assertRaisesRegex(RuntimeError, "invalid harness root"):
            paths.harness_root()
        with patch.object(paths, "EVAL_ROOT", self.product / "eval"), patch.dict(os.environ, {}, clear=True):
            self.assertEqual(paths.harness_root(), self.product)

    def test_argument_overrides_environment_and_missing_build_is_clear(self):
        with patch.dict(os.environ, {"LEAN_HARNESS_ROOT": "/missing"}):
            self.assertEqual(paths.harness_root(self.product), self.product)
            with self.assertRaisesRegex(RuntimeError, "lake build harness"):
                paths.harness_binary(self.product)

    def test_proxy_accepts_matching_snapshot_but_not_another_checkout(self):
        self.assertEqual(paths.eval_tools_binary(self.product), self.proxy)
        self.identity["harness_root"] = str(self.root / "other")
        self.identity_path.write_text(json.dumps(self.identity))
        with self.assertRaisesRegex(RuntimeError, "different product checkout"):
            paths.eval_tools_binary(self.product)

    def test_proxy_rejects_changed_binary_or_missing_identity(self):
        self.proxy.write_text("changed executable")
        with self.assertRaisesRegex(RuntimeError, "proxy binary changed"):
            paths.eval_tools_binary(self.product)
        self.identity_path.unlink()
        with self.assertRaisesRegex(RuntimeError, "identity missing"):
            paths.eval_tools_binary(self.product)

    def test_proxy_rejects_source_change_and_added_source(self):
        source = self.product / "Harness/Core.lean"
        original = source.read_text()
        source.write_text("def fixture := 2\n")
        with self.assertRaisesRegex(RuntimeError, "source changed"):
            paths.eval_tools_binary(self.product)
        source.write_text(original)
        (self.product / "Harness/Added.lean").write_text("def extra := 3\n")
        with self.assertRaisesRegex(RuntimeError, "inventory changed"):
            paths.eval_tools_binary(self.product)

    def test_toolchain_mismatch_is_explicit(self):
        (self.product / "lean-toolchain").write_text("different\n")
        with self.assertRaisesRegex(RuntimeError, "lean-toolchain differs"):
            paths.harness_root(self.product)

    def test_compiler_overrides_must_match_pins(self):
        compiler = self.root / "compiler"
        compiler.write_text("#!/bin/sh\necho 'Lean (version 4.33.1, fixture)'\n")
        compiler.chmod(0o755)
        paths.require_compiler_version(compiler, "Lean", "4.33.1")
        with self.assertRaisesRegex(RuntimeError, "workspace pin"):
            paths.require_compiler_version(compiler, "Lean", "4.32.0")
        compiler.write_text("#!/bin/sh\necho 'rustc 1.97.1 (fixture)'\n")
        paths.require_compiler_version(compiler, "Rust", "1.97.1")
        with self.assertRaisesRegex(RuntimeError, "workspace pin"):
            paths.require_compiler_version(compiler, "Rust", "1.96.0")

    def fake_node(self, name, version):
        binary = self.root / name / 'bin/node'
        binary.parent.mkdir(parents=True)
        binary.write_text("#!/bin/sh\n[ -z \"$NODE_OPTIONS\" ] || exit 9\nprintf '%s\\n' '" + version + "'\n")
        binary.chmod(0o755)
        return binary

    def test_node_identity_binds_executable_version_hash_and_distribution(self):
        binary = self.fake_node('node-approved', 'v24.16.0')
        with patch.dict(os.environ, {'NODE_OPTIONS': '--require /untrusted'}):
            identity = paths.node_identity(binary=binary)
        self.assertEqual(identity['root'], str(binary.parent.parent))
        self.assertEqual(identity['version'], 'v24.16.0')
        self.assertEqual(identity['sha256'], sha(binary))
        self.assertEqual(paths.node_identity(expected=identity, binary=binary), identity)
        binary.write_text(binary.read_text() + '# changed executable\n')
        with self.assertRaisesRegex(RuntimeError, 'frozen identity'):
            paths.node_identity(expected=identity, binary=binary)

    def test_sanitized_path_cannot_silently_select_distro_node(self):
        distro = self.fake_node('distro', 'v18.20.4')
        approved = self.fake_node('node-approved', 'v24.16.0')
        # The coordinator's old clean environment drops NODE_BIN/custom PATH.
        # Reproduce that in an actual child, rather than mocking path discovery.
        program = ('import sys;sys.path.insert(0,' + repr(str(ROOT / 'runner')) +
                   ');from paths import node_identity;print(node_identity()["binary"])')
        clean = {'PATH': str(distro.parent), 'HOME': str(self.root), 'LANG': 'C.UTF-8'}
        failed = subprocess.run([sys.executable, '-c', program], env=clean, capture_output=True, text=True)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn('requires Node >=22.19.0', failed.stderr)
        admitted = subprocess.run([sys.executable, '-c', program],
            env={**clean, 'NODE_BIN': str(approved)}, capture_output=True, text=True)
        self.assertEqual(admitted.returncode, 0, admitted.stderr)
        self.assertEqual(admitted.stdout.strip(), str(approved))

    def test_node_rejects_system_root_and_invalid_version(self):
        with patch.object(paths, 'command_path', return_value=Path('/usr/bin/node')):
            with self.assertRaisesRegex(RuntimeError, 'dedicated distribution'):
                paths.node_identity()
        binary = self.fake_node('broken-node', 'not a version')
        with self.assertRaisesRegex(RuntimeError, 'invalid version'):
            paths.node_identity(binary=binary)

    def test_pi_preflight_requires_exact_completed_identity(self):
        identity = paths.node_identity(binary=self.fake_node('node-approved', 'v24.16.0'))
        marker = {'status': 'ok', 'nodeVersion': identity['version'],
                  'nodeSha256': identity['sha256'], 'model': 'claude-opus-5-5',
                  'piVersion': '1.5.0', 'providerRequests': 0}
        self.assertEqual(paths.validate_node_preflight(json.dumps(marker), identity, marker['model']), marker)
        for change in [{'nodeSha256': 'wrong'}, {'nodeVersion': 'v22.19.0'}, {'providerRequests': 1},
                       {'piVersion': 'other'}, {'status': 'started'}]:
            with self.assertRaisesRegex(RuntimeError, 'mismatch'):
                paths.validate_node_preflight(json.dumps({**marker, **change}), identity, marker['model'])
        with self.assertRaisesRegex(RuntimeError, 'completion marker'):
            paths.validate_node_preflight('started\n' + json.dumps(marker), identity, marker['model'])

    def test_runner_fails_before_reading_credentials_when_root_missing(self):
        env = {"PATH": os.environ.get("PATH", "/usr/bin:/bin"), "HOME": str(self.root), "LEAN_HARNESS_ROOT": str(self.root / "missing")}
        result = subprocess.run([sys.executable, ROOT / "runner/suite.py", "--key-file", "/missing/key",
                                 "--campaign-dir", self.root / "missing-ledger", "--allocation", "development",
                                 "--output", self.root / "never-created"], env=env, text=True,
                                capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 2)
        self.assertIn("invalid harness root", result.stderr)
        self.assertFalse((self.root / "never-created").exists())

    def test_freshness_check_requests_no_build_and_rejects_stale_binary(self):
        binary = self.product / ".lake/build/bin/harness"
        binary.parent.mkdir(parents=True)
        binary.write_bytes(self.proxy.read_bytes())
        binary.chmod(0o755)
        before = sha(binary)
        (self.product / "lake-manifest.json").write_text('{"packages":[]}')
        lake = self.root / "fake-lake"
        lake.write_text("#!/usr/bin/python3\nfrom pathlib import Path\nimport sys,json\n"
                        "Path(__file__).with_suffix('.args').write_text(json.dumps(sys.argv[1:]))\nsys.exit(3)\n")
        lake.chmod(0o755)
        with patch.dict(os.environ, {"LAKE_BIN": str(lake)}):
            with self.assertRaisesRegex(RuntimeError, "stale"):
                paths.require_fresh_harness(self.product)
        self.assertEqual(json.loads(lake.with_suffix('.args').read_text()),
                         ["--no-cache", "--no-build", "--rehash", "build", "harness"])
        self.assertEqual(sha(binary), before)

    def test_missing_dependency_fails_before_lake_can_fetch_it(self):
        binary = self.product / ".lake/build/bin/harness"
        binary.parent.mkdir(parents=True)
        binary.write_bytes(self.proxy.read_bytes())
        binary.chmod(0o755)
        (self.product / "lake-manifest.json").write_text(
            '{"packages":[{"name":"absent","type":"git"}]}')
        with patch("paths.subprocess.run") as run:
            with self.assertRaisesRegex(RuntimeError, "missing cached product dependency"):
                paths.require_fresh_harness(self.product)
            run.assert_not_called()


if __name__ == "__main__":
    unittest.main()
