#!/usr/bin/env python3
"""Exercise Lean -> Rust ABI values through the compiled test executable.

No mock runtime or C shim is involved. Python supplies independent filesystem,
SHA-256 and byte-level oracles. Each case repeats sensitive crossings 10,000 times
and compares descriptor counts. This is regression evidence, not memory-safety proof.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / ".lake/build/bin/runtime_contracts"


class NativeABI(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="harness-native-abi-")
        self.path = Path(self.temporary.name) / "路径-λ🙂"
        self.path.mkdir()

    def tearDown(self):
        self.temporary.cleanup()

    def request(self, case, **fields):
        result = subprocess.run(
            [str(BINARY)], input=json.dumps({"op": "nativeAbi", "case": case,
                                           "path": str(self.path), **fields}) + "\n",
            text=True, capture_output=True, timeout=30, check=True,
            env={"PATH": os.defpath, "HOME": self.temporary.name, "LANG": "C.UTF-8"})
        observed = json.loads(result.stdout)
        self.assertEqual(observed["status"], "ok", observed)
        self.assertEqual(observed["iterations"], 10_000)
        self.assertEqual(observed["fdBefore"], observed["fdAfter"], observed)
        return observed

    def test_binary_empty_unicode_and_borrowed_values(self):
        data = bytes(range(256)) + "λ🙂\x00終".encode()
        name = "文件-λ🙂.bin"
        (self.path / name).write_bytes(data)
        digest = hashlib.sha256(data).hexdigest()
        observed = self.request("bytes", name=name, bytes=list(data), digest=digest,
                                emptyDigest=hashlib.sha256(b"").hexdigest())
        self.assertEqual(observed["bytes"], list(data))
        self.assertEqual(observed["digest"], digest)
        self.assertEqual(observed["names"], [name])
        self.assertEqual((self.path / name).read_bytes(), data)

    def test_uint64_metadata_uint32_descriptors_errors_and_pair(self):
        name = "大きい-λ🙂.bin"
        size = (1 << 33) + 123
        with (self.path / name).open("wb") as handle:
            handle.truncate(size)  # Sparse: no multi-gigabyte allocation or read.
        (self.path / name).chmod(0o640)
        observed = self.request("metadata", name=name, size=size)
        self.assertEqual((observed["kind"], observed["size"], observed["mode"]), (1, size, 0o640))
        self.assertEqual(observed["missingKind"], 4)
        for field in ["largeReadRejected", "invalidFdRejected", "missingOpenRejected", "nulPathRejected"]:
            self.assertTrue(observed[field], field)
        self.assertEqual([p.name for p in self.path.iterdir()], [name])
        self.assertEqual((self.path / name).stat().st_size, size)

    def test_nonblocking_options_spawn_array_and_exit_255(self):
        data = b"\x00\xff\x80" + "λ🙂".encode()
        observed = self.request("process", bytes=list(data))
        self.assertEqual(observed["output"], list(data + "λ🙂".encode()))
        self.assertEqual(observed["written"], len(data))
        self.assertEqual(observed["exitCode"], 255)


if __name__ == "__main__":
    unittest.main()
