"""Artifact storage/retrieval contracts against real Lean IO and independent bytes.

Each driver invocation is a fresh process. The allowed metadata represents the
core's admitted registry; pure-core tests separately check that admission.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from runtime_contracts import FAULT_SHIM

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / ".lake/build/bin/runtime_contracts"


class Artifacts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fault_temp = tempfile.TemporaryDirectory()
        source = Path(cls.fault_temp.name) / "faults.c"
        source.write_text(FAULT_SHIM)
        cls.shim = source.with_suffix(".so")
        subprocess.run(["cc", "-shared", "-fPIC", "-O2", str(source), "-o", str(cls.shim), "-ldl"], check=True)

    @classmethod
    def tearDownClass(cls):
        cls.fault_temp.cleanup()

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.workspace = self.root / "workspace"
        self.workspace.mkdir()
        self.storage = self.root / "artifacts"

    def tearDown(self):
        self.temporary.cleanup()

    def call(self, name, args, **options):
        env = options.pop("env", None)
        request = {"op": "tool", "workspace": str(self.workspace), "artifactDir": str(self.storage),
                   "outputBytes": 16, "maxArtifactBytes": 4096, "maxSessionArtifactBytes": 8192,
                   "call": {"name": name, "args": args}, **options}
        result = subprocess.run([str(BIN)], input=json.dumps(request)+"\n", text=True,
                                capture_output=True, timeout=10, env=env)
        self.assertEqual(result.returncode, 0, result.stderr)
        return json.loads(result.stdout)

    def produce(self, expression="bytes(range(256))*3", **options):
        return self.call("process", {"argv": ["/usr/bin/python3", "-c",
            f"import os; os.write(1,{expression})"]}, **options)

    def read(self, ref, offset=0, length=65536, **options):
        return self.call("artifact", {"id": ref["id"], "offset": offset, "length": length},
                         artifacts=[ref], outputBytes=512, **options)

    def test_ranges_reconstruct_binary_and_split_unicode_after_reopen(self):
        expected = bytes(range(256))*3 + "λ🙂終".encode()
        result = self.produce("bytes(range(256))*3+'λ🙂終'.encode()")
        self.assertEqual(result["status"], "ok", result)
        ref = result["artifacts"][0]
        self.assertEqual(ref["sha256"], hashlib.sha256(expected).hexdigest())
        recovered, offset = b"", 0
        while offset < len(expected):
            result = self.read(ref, offset, 37)
            self.assertEqual(result["status"], "ok", result)
            self.assertLessEqual(len(result["text"].encode()), 512)
            part = json.loads(result["text"])
            data = bytes.fromhex(part["content"]) if part["encoding"] == "hex" else part["content"].encode()
            self.assertEqual(part["nextOffset"], offset + len(data))
            self.assertGreater(part["nextOffset"], offset)
            recovered += data; offset = part["nextOffset"]
        self.assertEqual(recovered, expected)
        end = json.loads(self.read(ref, offset)["text"])
        self.assertTrue(end["endOfRetainedContent"])
        self.assertEqual(end["content"], "")
        for offset, length in [(len(expected)+1, 1), (0, 0), (0, 65537)]:
            self.assertEqual(self.read(ref, offset, length)["status"], "failed")

    def test_unknown_or_foreign_ids_never_read_arbitrary_paths(self):
        ref = self.produce()["artifacts"][0]
        unknown = self.call("artifact", {"id": ref["id"], "offset": 0, "length": 20}, outputBytes=512)
        self.assertEqual(unknown["status"], "failed")
        other = self.root / "other-artifacts"; other.mkdir()
        original = self.storage; self.storage = other
        try: self.assertEqual(self.read(ref)["status"], "failed")
        finally: self.storage = original
        for forged in ["../journal.jsonl", str(self.root / "credentials"), "a-"+"0"*64]:
            invalid = {**ref, "id": forged}
            self.assertEqual(self.read(invalid)["status"], "failed")

    def test_blob_and_metadata_corruption_are_rejected(self):
        ref = self.produce()["artifacts"][0]
        blob = self.storage / (ref["id"]+".blob")
        metadata = self.storage / (ref["id"]+".json")
        original_blob, original_metadata = blob.read_bytes(), metadata.read_bytes()
        for value in [b"private-sentinel", original_blob[:-1]]:
            blob.write_bytes(value)
            result = self.read(ref)
            self.assertEqual(result["status"], "failed")
            self.assertNotIn("private-sentinel", result["text"])
        blob.write_bytes(original_blob)
        for value in [b"{broken", b"x"*4097,
                      json.dumps({**ref, "label": "stderr"}).encode()]:
            metadata.write_bytes(value)
            self.assertEqual(self.read(ref)["status"], "failed")
        metadata.write_bytes(original_metadata)
        self.assertEqual(self.read(ref)["status"], "ok")

    def test_symlink_and_matching_content_hardlink_substitution_rejected(self):
        ref = self.produce()["artifacts"][0]
        for suffix in [".blob", ".json"]:
            path = self.storage / (ref["id"]+suffix)
            original = path.read_bytes()
            outside = self.root / ("outside"+suffix)
            outside.write_bytes(original)
            for hardlink in [False, True]:
                path.unlink()
                if hardlink: os.link(outside, path)
                else: path.symlink_to(outside)
                self.assertEqual(self.read(ref)["status"], "failed")
                path.unlink(); path.write_bytes(original)
            outside.unlink()

    def test_orphan_bytes_count_against_quota_and_exhaustion_is_visible(self):
        self.storage.mkdir()
        (self.storage / "unfinished.blob").write_bytes(b"o"*11)
        result = self.produce("b'x'*80", maxArtifactBytes=64, maxSessionArtifactBytes=64)
        ref = result["artifacts"][0]
        self.assertEqual((ref["storedBytes"], ref["totalBytes"], ref["truncated"]), (53, 80, True))
        exhausted = self.produce("b'y'*80", maxArtifactBytes=64, maxSessionArtifactBytes=64)
        empty = exhausted["artifacts"][0]
        self.assertEqual((empty["storedBytes"], empty["truncated"]), (0, True))
        retained = json.loads(self.read(empty)["text"])
        self.assertTrue(retained["endOfRetainedContent"])
        self.assertTrue(retained["truncated"])
        # Metadata has a separate bounded allowance; only output blobs count here.
        self.assertEqual(sum(p.stat().st_size for p in self.storage.iterdir() if not p.name.endswith('.json')), 64)

    def test_metadata_entry_exhaustion_leaves_no_new_partial_publication(self):
        self.storage.mkdir()
        for index in range(4094): (self.storage / f"existing-{index}.json").write_bytes(b"")
        result = self.produce("b'x'*80")
        self.assertEqual(result["status"], "uncertain", result)
        self.assertEqual(len(list(self.storage.iterdir())), 4094)

    def test_write_and_flush_failures_after_effect_preserve_uncertainty(self):
        for failure in ["HARNESS_TEST_FAIL_ARTIFACT_WRITE", "HARNESS_TEST_FAIL_FSYNC",
                        "HARNESS_TEST_FAIL_DIRECTORY_FSYNC"]:
            with self.subTest(failure=failure):
                env = {**os.environ, "LD_PRELOAD": str(self.shim), failure: "1"}
                result = self.call("process", {"argv": ["/usr/bin/python3", "-c",
                    "import pathlib,os; pathlib.Path('effect').write_text('done'); os.write(1,b'x'*100)"]}, env=env)
                self.assertEqual(result["status"], "uncertain", result)
                self.assertEqual((self.workspace / "effect").read_text(), "done")
                self.assertEqual(result.get("artifacts", []), [])


if __name__ == "__main__":
    unittest.main()
