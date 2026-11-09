"""Byte extraction ignores candidate Git code/config and preserves real changes."""
import io
from contextlib import contextmanager
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "runner"))
import workspace_snapshot as snapshots


def archive(entries):
    data = io.BytesIO()
    with tarfile.open(fileobj=data, mode="w") as stream:
        root = tarfile.TarInfo(".")
        root.type = tarfile.DIRTYPE
        stream.addfile(root)
        for name, value in entries:
            member = tarfile.TarInfo("./" + name)
            if isinstance(value, tuple):
                member.type, member.linkname = value
                stream.addfile(member)
            else:
                member.size = len(value)
                member.mode = 0o644
                stream.addfile(member, io.BytesIO(value))
    data.seek(0)
    return data


class WorkspaceSnapshots(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="trusted-extraction-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.store = snapshots._new_store(self.root / "baseline")

    def baseline(self, entries):
        manifest, _ = snapshots._read_snapshot(archive(entries), self.store)
        path = self.root / "baseline-manifest.json"
        snapshots._save(path, manifest)
        return {"store": str(self.store), "baseline_manifest": str(path),
                "baseline_tree": snapshots._tree(self.store, manifest)}

    def compare(self, baseline, entries):
        output = self.root / "candidate"
        output.mkdir()
        return snapshots._compare_snapshot(archive(entries), output, baseline)

    def test_candidate_git_filters_hooks_and_diff_are_inert(self):
        baseline = self.baseline([("src/code.py", b"value=0\n"), ("tests/test_code.py", b"assert value==0\n")])
        marker = self.root / "executed-candidate-code"
        script = "sh -c 'echo executed > " + str(marker) + "'"
        config = ("[diff]\n external = " + script + "\n[filter \"fixture\"]\n clean = " + script +
                  "\n[core]\n hooksPath = /candidate-hooks\n").encode()
        result = self.compare(baseline, [
            (".git/config", config), (".git/hooks/pre-commit", script.encode()),
            (".gitattributes", b"*.py filter=fixture diff=fixture working-tree-encoding=UTF-16\n"),
            (".gitignore", b"*\n"), ("src/code.py", b"value=1\n"),
            ("tests/test_code.py", b"assert True\n"), ("new.py", b"new=1\n")])
        self.assertFalse(marker.exists())
        self.assertIn("tests/test_code.py", result["existing_changed_paths"])
        self.assertIn("new.py", result["changed_paths"])
        text = Path(result["patch_path"]).read_text()
        self.assertIn("+value=1", text)
        self.assertIn("+assert True", text)
        self.assertNotIn(".git/config", text)

    def test_patch_reconstructs_exact_binary_symlink_and_text_bytes(self):
        baseline = self.baseline([("one.txt", b"old\r\n"), ("remove.txt", b"gone")])
        result = self.compare(baseline, [("one.txt", b"new\r\n"), ("binary.dat", bytes(range(256))),
                                         ("link", (tarfile.SYMTYPE, "/outside/never-follow")),
                                         ("unicodé.txt", "λ\n".encode())])
        snapshots._git(self.store, "read-tree", baseline["baseline_tree"])
        snapshots._git(self.store, "apply", "--cached", "--binary", "--whitespace=nowarn", result["patch_path"])
        self.assertEqual(snapshots._git(self.store, "write-tree").decode().strip(), result["candidate_tree"])
        self.assertEqual(result["existing_changed_paths"], ["one.txt", "remove.txt"])

    def test_only_new_standard_caches_are_excluded(self):
        baseline = self.baseline([("tests/__pycache__/fixture.pyc", b"tracked fixture"),
                                  ("source.py", b"old")])
        result = self.compare(baseline, [("tests/__pycache__/fixture.pyc", b"changed fixture"),
                                         ("source.py", b"new"), ("__pycache__/new.pyc", b"cache"),
                                         (".pytest_cache/v/cache/nodeids", b"[]"),
                                         ("dist/new.py", b"source"), ("build/new.txt", b"data")])
        self.assertEqual(result["ignored_new_cache_paths"], [".pytest_cache/v/cache/nodeids", "__pycache__/new.pyc"])
        self.assertIn("tests/__pycache__/fixture.pyc", result["changed_paths"])
        self.assertIn("dist/new.py", result["changed_paths"])
        self.assertIn("build/new.txt", result["changed_paths"])
        inventory = json.loads(Path(result["candidate_manifest"]).read_text())
        self.assertIn("__pycache__/new.pyc", inventory)

    def test_paths_links_and_special_entries_are_rejected_without_extraction(self):
        cases = [[("../escape", b"bad")], [("x", (tarfile.LNKTYPE, "/outside"))],
                 [("x", (tarfile.FIFOTYPE, ""))], [("same", b"1"), ("same", b"2")],
                 [("parent", (tarfile.SYMTYPE, "/outside")), ("parent/child", b"bad")]]
        for entries in cases:
            with self.subTest(entries=entries), self.assertRaises(snapshots.SnapshotError):
                snapshots._read_snapshot(archive(entries), self.store)
        self.assertFalse((self.root / "escape").exists())

    def test_ambient_git_configuration_cannot_execute(self):
        marker = self.root / "ambient-executed"
        with patch.dict(os.environ, {"GIT_EXTERNAL_DIFF": "touch " + str(marker),
                                    "GIT_CONFIG_COUNT": "1", "GIT_CONFIG_KEY_0": "diff.external",
                                    "GIT_CONFIG_VALUE_0": "touch " + str(marker)}):
            baseline = self.baseline([("file", b"old")])
            self.compare(baseline, [("file", b"new")])
        self.assertFalse(marker.exists())

    def test_file_and_entry_caps_fail_explicitly(self):
        with patch.dict(snapshots.LIMITS, {"file_bytes": 2}):
            with self.assertRaisesRegex(snapshots.SnapshotError, "file byte"):
                snapshots._read_snapshot(archive([("large", b"123")]), self.store)
        with patch.dict(snapshots.LIMITS, {"entries": 1}):
            with self.assertRaisesRegex(snapshots.SnapshotError, "entry"):
                snapshots._read_snapshot(archive([("file", b"1")]), self.store)

    def test_running_candidate_is_rejected_before_archive(self):
        with patch.object(subprocess, "check_output", return_value="true\n"), \
             patch.object(snapshots, "_docker_archive") as opening:
            with self.assertRaisesRegex(snapshots.SnapshotError, "stopped"):
                snapshots.capture_candidate_after_stop("fixture", "/workspace", self.root / "out", {})
            opening.assert_not_called()

    def test_unchanged_snapshot_has_valid_empty_patch(self):
        baseline = self.baseline([("source.py", b"same\n")])
        result = self.compare(baseline, [("source.py", b"same\n"), (".git/config", b"changed metadata")])
        self.assertEqual(result["changed_paths"], [])
        self.assertEqual(Path(result["patch_path"]).read_bytes(), b"")
        self.assertEqual(result["baseline_tree"], result["candidate_tree"])

    def test_regular_result_reader_rejects_links_and_oversize(self):
        @contextmanager
        def result_archive(*_):
            # Docker's single-file archive has no directory header.
            data = io.BytesIO()
            with tarfile.open(fileobj=data, mode="w") as stream:
                member = tarfile.TarInfo("result.json")
                if symbolic:
                    member.type, member.linkname = tarfile.SYMTYPE, "/outside"
                    stream.addfile(member)
                else:
                    member.size = 2
                    stream.addfile(member, io.BytesIO(b"{}"))
            data.seek(0)
            yield data
        symbolic = False
        with patch.object(snapshots, "_docker_stream", result_archive):
            self.assertEqual(snapshots.read_regular_file("fixture", "/tmp/result.json", 2), b"{}")
            with self.assertRaises(snapshots.SnapshotError):
                snapshots.read_regular_file("fixture", "/tmp/result.json", 1)
            symbolic = True
            with self.assertRaises(snapshots.SnapshotError):
                snapshots.read_regular_file("fixture", "/tmp/result.json", 100)

    def test_regular_session_mirror_is_owned_and_byte_exact(self):
        destination = self.root / "session-mirror"
        result = snapshots._export_regular_tree(archive([
            ("journal.jsonl", b'{"record":"fixture"}\n'), ("lock", b""),
            ("artifacts/a-fixture.blob", bytes(range(256))),
            ("artifacts/a-fixture.json", b'{"bytes":256}\n')]), destination)
        self.assertEqual((destination / "artifacts/a-fixture.blob").read_bytes(), bytes(range(256)))
        self.assertEqual(result["files"]["artifacts/a-fixture.blob"]["bytes"], 256)
        for name in result["files"]:
            info = (destination / name).stat()
            self.assertEqual(info.st_uid, os.getuid())
            self.assertEqual(info.st_mode & 0o777, 0o600)
            self.assertEqual(info.st_nlink, 1)

    def test_regular_session_mirror_rejects_bad_entries_and_caps(self):
        cases = [[("../escape", b"bad")], [("journal.jsonl", (tarfile.SYMTYPE, "/outside"))],
                 [("journal.jsonl", (tarfile.LNKTYPE, "other"))],
                 [("pipe", (tarfile.FIFOTYPE, ""))], [("same", b"1"), ("same", b"2")]]
        for index, entries in enumerate(cases):
            with self.subTest(entries=entries), self.assertRaises(snapshots.SnapshotError):
                snapshots._export_regular_tree(archive(entries), self.root / ("bad" + str(index)))
        for index, (limits, entries) in enumerate([
            ({"file_bytes": 1}, [("journal.jsonl", b"too big")]),
            ({"total_bytes": 2}, [("one", b"12"), ("two", b"3")]),
            ({"entries": 1}, [("journal.jsonl", b"x")]),
            ({"depth": 1}, [("nested/file", b"x")])]):
            with self.subTest(limits=limits), patch.dict(snapshots.SESSION_LIMITS, limits), \
                 self.assertRaises(snapshots.SnapshotError):
                snapshots._export_regular_tree(archive(entries), self.root / ("limit" + str(index)))

    def test_final_session_mirror_requires_stopped_candidate(self):
        with patch.object(subprocess, "check_output", return_value="true\n"), \
             patch.object(snapshots, "_docker_archive") as opening:
            with self.assertRaisesRegex(snapshots.SnapshotError, "stopped"):
                snapshots.mirror_session_after_stop("fixture", "/sessions/session", self.root / "mirror")
            opening.assert_not_called()

    def test_session_path_aliases_and_ancestor_conflicts_cannot_escape(self):
        # Construct exact archive names here: the ordinary fixture deliberately
        # adds './', which would turn an absolute name into a relative alias.
        outside = self.root / "outside"
        outside.write_bytes(b"preserve")
        cases = [
            [(str(outside), b"overwrite")],
            [("nested/../../outside", b"overwrite")],
            [("journal.jsonl", b"one"), ("./journal.jsonl", b"two")],
            [("nested/file", b"one"), ("nested//file", b"two")],
            [("artifacts", (tarfile.SYMTYPE, str(self.root))), ("artifacts/outside", b"overwrite")],
            [("artifacts/file", b"one"), ("artifacts", b"replacement")],
            [("artifacts", b"one"), ("artifacts/file", b"replacement")],
        ]
        for index, entries in enumerate(cases):
            data = io.BytesIO()
            with tarfile.open(fileobj=data, mode="w") as stream:
                for name, value in entries:
                    member = tarfile.TarInfo(name)
                    if isinstance(value, tuple):
                        member.type, member.linkname = value
                        stream.addfile(member)
                    else:
                        member.size = len(value)
                        stream.addfile(member, io.BytesIO(value))
            data.seek(0)
            with self.subTest(entries=entries), self.assertRaises((snapshots.SnapshotError, OSError)):
                snapshots._export_regular_tree(data, self.root / ("conflict" + str(index)))
            self.assertEqual(outside.read_bytes(), b"preserve")
        self.assertFalse((self.root / "journal.jsonl").exists())


if __name__ == "__main__":
    unittest.main()
