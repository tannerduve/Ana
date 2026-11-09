#!/usr/bin/env python3
"""Trusted session storage must be outside the direct-file tool workspace."""
import json
import os
import shutil
from pathlib import Path
import subprocess
import tempfile
import unittest

from integration import response
from journal_fixture import journal_read, journal_append


ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / ".lake/build/bin/harness"


class SessionBoundaries(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="harness-boundary-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.workspace = self.root / "workspace"
        self.workspace.mkdir()
        self.home = self.root / "home"
        self.home.mkdir()
        self.session = self.root / "session"
        self.config = self.root / "config.json"
        self.config.write_text(json.dumps({"model": "scripted", "commands": "deny"}))
        self.script = self.root / "script.json"
        self.script.write_text(json.dumps([response(text="done")]))
        self.env = {"PATH": os.defpath, "HOME": str(self.home), "LANG": "C.UTF-8"}

    def cli(self, *arguments):
        return subprocess.run([str(BINARY), *map(str, arguments)], cwd=self.workspace if self.workspace.is_dir() else self.root,
                              env=self.env, text=True, capture_output=True, timeout=15)

    def run_session(self, session=None):
        args = ["run", "--workspace", self.workspace, "--config", self.config,
                "--task", "finish", "--script", self.script, "--json"]
        if session is not None:
            args += ["--session", session]
        return self.cli(*args)

    def assert_overlap(self, result):
        self.assertEqual(result.returncode, 2, result.stderr + result.stdout)
        self.assertIn("session and workspace must not overlap", result.stderr)
        self.assertNotIn('"event":"intent"', result.stdout)

    def test_default_from_workspace_uses_external_home_state(self):
        result = self.run_session()
        self.assertEqual(result.returncode, 0, result.stderr)
        event = json.loads(result.stdout.splitlines()[0])
        path = Path(event["session"])
        self.assertEqual(path.parent, self.home / ".local/state/lean-harness/sessions")
        self.assertTrue((path / "journal.jsonl").is_file())
        self.assertFalse((self.workspace / ".sessions").exists())
        self.assertEqual(self.cli("resume", path).returncode, 0)

    def test_absolute_xdg_state_home_is_honored(self):
        self.env["XDG_STATE_HOME"] = str(self.root / "state")
        result = self.run_session()
        self.assertEqual(result.returncode, 0, result.stderr)
        path = Path(json.loads(result.stdout.splitlines()[0])["session"])
        self.assertEqual(path.parent, self.root / "state/lean-harness/sessions")

    def test_relative_xdg_state_home_does_not_move_storage_into_workspace(self):
        self.env["XDG_STATE_HOME"] = "relative-state"
        result = self.run_session()
        self.assertEqual(result.returncode, 0, result.stderr)
        path = Path(json.loads(result.stdout.splitlines()[0])["session"])
        self.assertEqual(path.parent, self.home / ".local/state/lean-harness/sessions")
        self.assertFalse((self.workspace / "relative-state").exists())

    def test_explicit_inside_equal_and_ancestor_paths_are_rejected(self):
        for path in [self.workspace / "private/new-session", self.workspace, self.root]:
            with self.subTest(path=path):
                self.assert_overlap(self.run_session(path))
        self.assertFalse((self.workspace / "private").exists())
        self.assertFalse((self.workspace / "journal.jsonl").exists())

    def test_existing_symlink_parent_cannot_hide_missing_session_suffix(self):
        alias = self.root / "alias"
        alias.symlink_to(self.workspace, target_is_directory=True)
        self.assert_overlap(self.run_session(alias / "missing/session"))
        self.assertFalse((self.workspace / "missing").exists())

    def test_dotdot_is_resolved_after_existing_symlink(self):
        child = self.workspace / "child"
        child.mkdir()
        alias = self.root / "alias"
        alias.symlink_to(child, target_is_directory=True)
        self.assert_overlap(self.run_session(str(alias) + "/../session"))
        self.assertFalse((self.workspace / "session").exists())

    def test_sibling_with_common_string_prefix_remains_valid(self):
        session = self.root / "workspace-sessions/session"
        result = self.run_session(session)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.cli("resume", session).returncode, 0)

    def test_forged_framed_workspace_is_rejected_before_resume_dispatch(self):
        self.assertEqual(self.run_session(self.session).returncode, 0)
        journal = self.session / "journal.jsonl"
        initial = journal_read(journal)["records"][0]
        initial["config"]["workspace"] = str(self.session)
        initial["script"] = [response([("bad", "create", {"path": "mutated", "content": "bad"})])]
        journal.unlink()
        journal_append(journal, initial)
        before = journal.read_bytes()
        self.assert_overlap(self.cli("resume", self.session, "--json"))
        self.assertEqual(journal.read_bytes(), before)
        self.assertFalse((self.session / "mutated").exists())

    def test_changed_workspace_alias_is_rechecked_on_resume(self):
        self.assertEqual(self.run_session(self.session).returncode, 0)
        self.workspace.rmdir()
        self.workspace.symlink_to(self.session, target_is_directory=True)
        self.assert_overlap(self.cli("resume", self.session, "--json"))

    def test_offline_inspection_and_replay_survive_missing_workspace(self):
        self.assertEqual(self.run_session(self.session).returncode, 0)
        self.workspace.rmdir()
        journal = self.session / "journal.jsonl"
        before = journal.read_bytes()
        for command in ["inspect", "replay"]:
            result = self.cli(command, self.session)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(json.loads(result.stdout)["terminal"])
        self.assertEqual(self.cli("resume", self.session).returncode, 2)
        self.assertEqual(journal.read_bytes(), before)

    def test_copied_checkpoint_cannot_resume_under_a_second_lock(self):
        result = self.cli("run", "--workspace", self.workspace, "--config", self.config,
                          "--task", "finish", "--script", self.script,
                          "--session", self.session, "--yield-after", "1")
        self.assertEqual(result.returncode, 75, result.stderr)
        copied = self.root / "copied-session"
        shutil.copytree(self.session, copied)
        journal = copied / "journal.jsonl"
        before = journal.read_bytes()
        refused = self.cli("resume", copied)
        self.assertEqual(refused.returncode, 2, refused.stderr)
        self.assertIn("relocated sessions cannot resume", refused.stderr)
        self.assertEqual(journal.read_bytes(), before)
        self.assertEqual(self.cli("inspect", copied).returncode, 0)
        self.assertEqual(self.cli("resume", self.session).returncode, 0)

    def test_new_top_level_parent_resumes_without_path_change(self):
        # The missing first component exists only in a private mount namespace;
        # this regression never creates a directory under the host's root.
        code = r'''
import json
from pathlib import Path
import subprocess
session = '/new-session-parent/deeper/session'
assert not Path('/new-session-parent').exists()
def cli(*args):
    return subprocess.run(['/harness', *args], text=True, capture_output=True, timeout=10)
first = cli('run', '--workspace', '/fixture/workspace', '--config', '/fixture/config.json',
            '--task', 'finish', '--script', '/fixture/script.json', '--session', session,
            '--yield-after', '1', '--json')
assert first.returncode == 75, (first.returncode, first.stderr)
journal = Path(session) / 'journal.jsonl'
initial = json.loads(journal.read_text().splitlines()[0])['record']
assert initial['session'] == session, initial['session']
resumed = cli('resume', session, '--json')
assert resumed.returncode == 0, (resumed.returncode, resumed.stderr)
inspected, replayed = cli('inspect', session), cli('replay', session)
assert inspected.returncode == replayed.returncode == 0
assert json.loads(inspected.stdout) == json.loads(replayed.stdout)
assert json.loads(inspected.stdout)['terminal'] is True
before = journal.read_bytes()
assert cli('resume', session, '--json').returncode == 0
assert journal.read_bytes() == before
'''
        command = ["/usr/bin/bwrap", "--unshare-user", "--uid", "0", "--gid", "0",
                   "--unshare-pid", "--unshare-net", "--die-with-parent",
                   "--ro-bind", "/usr", "/usr", "--ro-bind", "/lib", "/lib",
                   "--ro-bind", "/lib64", "/lib64", "--proc", "/proc", "--dev", "/dev",
                   "--tmpfs", "/tmp", "--ro-bind", str(BINARY), "/harness",
                   "--bind", str(self.root), "/fixture", "--chdir", "/fixture/workspace",
                   "--setenv", "HOME", "/fixture/home", "--", "/usr/bin/python3", "-c", code]
        result = subprocess.run(command, env=self.env, text=True, capture_output=True, timeout=40)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
