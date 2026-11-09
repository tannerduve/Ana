"""Actual CLI capability admission, frozen restrictions, and policy-file boundaries.

All model messages are scripted. Process probes only write temporary markers;
exact launch permission is deliberately not claimed to confine process effects.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from integration import response
from journal_fixture import journal_append


ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / ".lake/build/bin/harness"


def file_access(kind, path, scope="exact"):
    return {"kind": kind, "scope": {"kind": scope, "path": path}}


def resource(action, value=None, application="inventory"):
    scope = {"kind": "all"} if value is None else {"kind": "exact", "value": value}
    return {"kind": "resource", "application": application, "action": action, "scope": scope}


class CapabilityPolicy(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="harness-capabilities-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.ws = self.root / "workspace"
        self.ws.mkdir()
        self.home = self.root / "home"
        self.home.mkdir()
        self.session = self.root / "session"
        self.config = {"model": "scripted-capabilities", "commands": "allow",
                       "compactionEnabled": False, "maxContextBytes": 200000,
                       "maxModelAttempts": 10, "maxToolCalls": 40,
                       "operationTimeoutMs": 5000, "maxElapsedMs": 30000}
        self.env = {"PATH": os.defpath, "HOME": str(self.home), "LANG": "C.UTF-8"}

    def json_file(self, name, value):
        path = self.root / name
        path.write_text(json.dumps(value), encoding="utf-8")
        return path

    def cli(self, *args, expected=0, stdin=None):
        result = subprocess.run([str(BIN), *map(str, args)], cwd=self.root, env=self.env,
                                input=stdin, text=True, capture_output=True, timeout=30)
        self.assertEqual(result.returncode, expected, result.stderr + result.stdout)
        return result

    def run_script(self, script, *, extra=(), expected=0, application="coding", stdin=None):
        config = self.json_file("config.json", self.config)
        source = self.json_file("script.json", script)
        args = ["run", "--application", application, "--config", config,
                "--task", "Exercise only the declared temporary resources",
                "--session", self.session, "--script", source, "--json"]
        if application == "coding":
            args += ["--workspace", self.ws]
        return self.cli(*args, *extra, expected=expected, stdin=stdin)

    def inspect(self):
        return json.loads(self.cli("inspect", self.session).stdout)["state"]

    def records(self):
        return [json.loads(line)["record"]
                for line in (self.session / "journal.jsonl").read_text().splitlines()]

    def tool_ids(self):
        return [row["action"]["call"]["id"] for row in self.records()
                if row["kind"] == "intent" and row["action"]["kind"] == "tool"]

    def results(self):
        return {block["tool_use_id"]: block for message in self.inspect()["history"]
                for block in message["content"] if block["type"] == "tool_result"}

    def assert_denied(self, results, *ids):
        for ident in ids:
            self.assertTrue(results[ident]["is_error"], ident)
            self.assertIn("policy denied", results[ident]["content"], ident)
            self.assertNotIn(ident, self.tool_ids())

    def test_policy_check_direction_and_restriction_are_conjunctive(self):
        parent = [[file_access("read", "src", "tree")]]
        limit = [file_access("read", "src/file")]
        parent_file = self.json_file("parent.json", parent)
        limit_file = self.json_file("limit.json", limit)
        combined = json.loads(self.cli("policy", "restrict", parent_file, limit_file).stdout)
        self.assertEqual(combined, parent + [limit])
        child_file = self.json_file("child.json", combined)
        self.assertEqual(json.loads(self.cli("policy", "check", parent_file, child_file).stdout),
                         {"status": "contained"})
        self.assertEqual(json.loads(self.cli("policy", "check", child_file, parent_file,
                                           expected=3).stdout), {"status": "not_established"})
        everything = self.json_file("everything.json", [{"kind": "everything"}])
        unchanged_authority = json.loads(self.cli("policy", "restrict", parent_file, everything).stdout)
        self.assertEqual(unchanged_authority, parent + [[{"kind": "everything"}]])
        empty = self.json_file("empty-limit.json", [])
        self.assertEqual(json.loads(self.cli("policy", "restrict", parent_file, empty).stdout),
                         parent + [[]])

    def test_omitted_policy_keeps_existing_default_authority(self):
        self.run_script([response([("create", "create", {"path": "default", "content": "allowed"})]),
                         response()])
        self.assertEqual(self.inspect()["config"]["capabilityPolicy"], [])
        self.assertEqual(self.tool_ids(), ["create"])
        self.assertEqual((self.ws / "default").read_text(), "allowed")

    def test_recursive_read_edit_create_and_component_prefixes(self):
        (self.ws / "src").mkdir()
        (self.ws / "src2").mkdir()
        original = "alpha\nneedle\n"
        (self.ws / "src/file").write_text(original)
        (self.ws / "src2/secret").write_text("DO_NOT_DISCLOSE")
        (self.ws / "single").write_text("single needle")
        self.config["capabilityPolicy"] = [[file_access("read", "src", "tree"),
                                            file_access("write", "src/file"),
                                            file_access("write", "out"), file_access("read", "single")]]
        calls = [("list", "list", {"path": "src"}),
                 ("read", "read", {"path": "src/file"}),
                 ("alias-read", "read", {"path": "src/./file"}),
                 ("search", "search", {"path": "src", "query": "needle"}),
                 ("edit", "edit", {"path": "src/file", "old": "alpha", "new": "beta",
                                    "expectedSha256": hashlib.sha256(original.encode()).hexdigest()}),
                 ("create", "create", {"path": "out", "content": "allowed"}),
                 ("root-list", "list", {"path": "."}),
                 ("root-search", "search", {"path": ".", "query": "DO_NOT_DISCLOSE"}),
                 ("sibling", "read", {"path": "src2/secret"}),
                 ("write-sibling", "create", {"path": "src2/new", "content": "blocked"}),
                 ("exact-not-tree", "search", {"path": "single", "query": "needle"})]
        self.run_script([response(calls), response()])
        found = self.results()
        self.assertEqual(self.tool_ids(), ["list", "read", "alias-read", "search", "edit", "create"])
        self.assertEqual(self.inspect()["toolDispatches"], 6)
        for ident in self.tool_ids():
            self.assertFalse(found[ident]["is_error"])
        self.assert_denied(found, "root-list", "root-search", "sibling", "write-sibling", "exact-not-tree")
        self.assertNotIn("DO_NOT_DISCLOSE", "".join(row["content"] for row in found.values()))
        self.assertEqual((self.ws / "src/file").read_text(), "beta\nneedle\n")
        self.assertEqual((self.ws / "out").read_text(), "allowed")
        self.assertFalse((self.ws / "src2/new").exists())

    def test_allowed_lexical_path_does_not_bypass_existing_symlink_refusal(self):
        (self.ws / "src").mkdir()
        secret = self.ws / "private"
        secret.write_text("PRIVATE_SENTINEL")
        (self.ws / "src/link").symlink_to(secret)
        self.config["capabilityPolicy"] = [[file_access("read", "src", "tree"),
                                            file_access("write", "src", "tree")]]
        self.run_script([response([("read-link", "read", {"path": "src/link"}),
                                   ("write-link", "create", {"path": "src/link", "content": "bad",
                                                             "overwrite": True})]), response()])
        found = self.results()
        self.assertEqual(self.tool_ids(), ["read-link", "write-link"])
        self.assertTrue(all(row["is_error"] for row in found.values()))
        self.assertNotIn("PRIVATE_SENTINEL", json.dumps(found))
        self.assertEqual(secret.read_text(), "PRIVATE_SENTINEL")
        self.assertTrue((self.ws / "src/link").is_symlink())

    def test_edit_needs_read_and_write_before_witness_preparation(self):
        # Wrong preimage would produce preparation failure if the adapter were reached.
        target = self.ws / "protected"
        target.write_text("unchanged")
        self.config["toolPolicy"] = "ask"
        self.config["capabilityPolicy"] = [[file_access("write", "protected")]]
        self.run_script([response([("denied-edit", "edit", {
            "path": "protected", "old": "unchanged", "new": "changed", "expectedSha256": "0" * 64})]),
            response()], stdin="yes\n")
        self.assert_denied(self.results(), "denied-edit")
        self.assertEqual(target.read_text(), "unchanged")
        self.assertFalse(any(row.get("action", {}).get("kind") in {"ask", "tool"}
                             for row in self.records()))
        self.assertFalse(any(row.get("editWitness") for row in self.records()))

    def test_exact_process_argv_and_cwd_and_existing_command_ceiling(self):
        (self.ws / "src").mkdir()
        code = "from pathlib import Path; Path('launched').write_text('once')"
        argv = [sys.executable, "-c", code]
        self.config["capabilityPolicy"] = [[{"kind": "process", "argv": argv, "cwd": "src"}]]
        calls = [("wrong-argument", "process", {"argv": argv + ["extra"], "cwd": "src"}),
                 ("wrong-cwd", "process", {"argv": argv, "cwd": "."}),
                 ("exact", "process", {"argv": argv, "cwd": "src"})]
        self.run_script([response(calls), response()])
        self.assertEqual(self.tool_ids(), ["exact"])
        self.assert_denied(self.results(), "wrong-argument", "wrong-cwd")
        self.assertFalse((self.ws / "launched").exists())
        self.assertEqual((self.ws / "src/launched").read_text(), "once")
        # This write has no direct-file write rule: process grants name launches,
        # not a promise to constrain that process's filesystem effects.
        self.session = self.root / "commands-deny-session"
        self.config["commands"] = "deny"
        (self.ws / "src/launched").unlink()
        self.run_script([response([("exact", "process", {"argv": argv, "cwd": "src"})]), response()])
        self.assert_denied(self.results(), "exact")
        self.assertFalse((self.ws / "src/launched").exists())

    def test_run_restriction_cannot_widen_and_empty_layer_denies(self):
        parent = [[file_access("write", "allowed")]]
        self.config["capabilityPolicy"] = parent
        limit = self.json_file("limit.json", [{"kind": "everything"}])
        self.run_script([response([("yes", "create", {"path": "allowed", "content": "yes"}),
                                   ("no", "create", {"path": "other", "content": "no"})]), response()],
                        extra=("--restrict-capabilities", limit))
        self.assertEqual(self.inspect()["config"]["capabilityPolicy"], parent + [[{"kind": "everything"}]])
        self.assert_denied(self.results(), "no")
        self.assertFalse((self.ws / "other").exists())
        self.session = self.root / "empty-session"
        limit.write_text("[]")
        self.run_script([response([("none", "create", {"path": "empty-blocked", "content": "no"})]),
                         response()], extra=("--restrict-capabilities", limit))
        self.assertEqual(self.inspect()["toolDispatches"], 0)
        self.assert_denied(self.results(), "none")

    def test_restart_continue_freeze_policy_and_ignore_changed_input_files(self):
        policy = [[file_access("write", "allowed")]]
        self.config["capabilityPolicy"] = [[{"kind": "everything"}]]
        limit = self.json_file("limit.json", policy[0])
        script = [response([("first", "create", {"path": "allowed", "content": "first"})]), response(),
                  response([("second-denied", "create", {"path": "other", "content": "bad"})]), response()]
        self.run_script(script, extra=("--restrict-capabilities", limit, "--yield-after", "2"), expected=75)
        frozen = self.inspect()["config"]["capabilityPolicy"]
        limit.write_text('[{"kind":"everything"}]')
        self.json_file("config.json", {"model": "changed", "capabilityPolicy": []})
        self.cli("resume", self.session, "--json")
        first = self.inspect()
        self.assertEqual(first["config"]["capabilityPolicy"], frozen)
        self.cli("continue", self.session, "--task", "Try another file", "--json")
        final = self.inspect()
        self.assertEqual(final["config"]["capabilityPolicy"], frozen)
        self.assertEqual(final["turn"], 1)
        self.assertEqual(final["modelAttempts"], 4)
        self.assertEqual(final["toolDispatches"], 1)
        self.assert_denied(self.results(), "second-denied")
        self.assertFalse((self.ws / "other").exists())
        self.assertEqual(json.loads(self.cli("replay", self.session).stdout)["state"], final)
        before = (self.session / "journal.jsonl").read_bytes()
        for command in ["resume", "continue"]:
            with self.subTest(command=command):
                args = [command, self.session, "--restrict-capabilities", limit]
                if command == "continue":
                    args += ["--task", "not admitted"]
                self.assertIn("cannot be overridden", self.cli(*args, expected=2).stderr)
                self.assertEqual((self.session / "journal.jsonl").read_bytes(), before)

    def inventory(self):
        self.config.pop("commands")
        self.config["applicationData"] = {"version": 1, "items": [
            {"sku": "A", "name": "Alpha", "warehouse": "north", "onHand": 10, "reorderPoint": 20},
            {"sku": "B", "name": "Beta", "warehouse": "south", "onHand": 8, "reorderPoint": 12}]}

    def test_inventory_namespaces_reservation_and_aggregate_rights(self):
        self.inventory()
        self.config["capabilityPolicy"] = [[resource("lookup", "A"), resource("reserve", "A"),
                                            resource("low_stock", "north"),
                                            resource("lookup", "B", application="coding")]]
        calls = [("reserve-A", "reserve", {"sku": "A", "units": 3}),
                 ("lookup-A", "lookup", {"sku": "A"}),
                 ("lookup-B", "lookup", {"sku": "B"}),
                 ("reserve-B", "reserve", {"sku": "B", "units": 2}),
                 ("north", "low_stock", {"warehouse": "north"}),
                 ("south", "low_stock", {"warehouse": "south"}),
                 ("totals", "warehouse_totals", {})]
        self.run_script([response(calls), response()], application="inventory")
        self.assertEqual(self.tool_ids(), ["reserve-A", "lookup-A", "north"])
        found = self.results()
        self.assert_denied(found, "lookup-B", "reserve-B", "south", "totals")
        value = json.loads(json.loads(found["lookup-A"]["content"])["text"])
        self.assertEqual(value["item"]["onHand"], 7)
        ledger = [json.loads(row)["record"] for row in (self.session / "inventory.jsonl").read_text().splitlines()]
        self.assertEqual(len(ledger), 2)
        self.assertEqual(ledger[1]["receipt"]["sku"], "A")
        self.assertEqual(ledger[1]["receipt"]["remaining"], 7)

    def test_inventory_reservation_needs_read_and_write_domain_rights(self):
        self.inventory()
        self.config["capabilityPolicy"] = [[resource("reserve", "A")]]
        self.run_script([response([("reserve", "reserve", {"sku": "A", "units": 1})]), response()],
                        application="inventory")
        self.assert_denied(self.results(), "reserve")
        self.assertEqual(len((self.session / "inventory.jsonl").read_text().splitlines()), 1)

    def test_malformed_policies_and_unknown_config_fields_fail_before_session(self):
        invalid = [None, {}, [None], [[{"kind": "unknown"}]],
                   [[{"kind": "everything", "extra": True}]],
                   [[{"kind": "read", "scope": {"kind": "tree", "path": "src", "extra": 1}}]],
                   [[file_access("read", "../outside", "tree")]],
                   [[{"kind": "process", "argv": "echo", "cwd": "."}]],
                   [[{"kind": "process", "argv": [], "cwd": "."}]],
                   [[{"kind": "resource", "application": "inventory", "action": "lookup",
                       "scope": {"kind": "all", "value": "A"}}]],
                   [[]] * 33]
        for index, policy in enumerate(invalid):
            with self.subTest(index=index):
                self.session = self.root / f"invalid-{index}"
                self.config["capabilityPolicy"] = policy
                self.run_script([response()], expected=2)
                self.assertFalse(self.session.exists())
        self.config["capabilityPolicy"] = []
        self.config["capabiltyPolicy"] = []
        self.session = self.root / "misspelled-config"
        self.assertIn("unknown configuration field", self.run_script([response()], expected=2).stderr)
        self.assertFalse(self.session.exists())

    def test_policy_command_bounds_files_and_options(self):
        parent = self.json_file("parent.json", [[]] * 32)
        limit = self.json_file("limit.json", [])
        self.cli("policy", "restrict", parent, limit, expected=2)
        self.cli("policy", "check", parent, expected=2)
        self.cli("policy", "check", parent, parent, "--json", expected=2)
        malformed = self.json_file("malformed.json", [{"kind": "everything"}])
        self.cli("policy", "check", malformed, parent, expected=2)
        oversized = self.root / "oversized.json"
        oversized.write_bytes(b" " * (1024 * 1024 + 1))
        self.cli("policy", "check", oversized, parent, expected=2)
        alias = self.root / "alias.json"
        alias.symlink_to(parent)
        self.cli("policy", "check", alias, parent, expected=2)
        self.assertIn("duplicate option", self.run_script([response()], extra=(
            "--restrict-capabilities", limit, "--restrict-capabilities", limit), expected=2).stderr)
        self.assertFalse(self.session.exists())

    def test_invalid_frozen_policy_refuses_resume_before_dispatch(self):
        self.config["capabilityPolicy"] = [[file_access("write", "allowed")]]
        self.run_script([response([("new", "create", {"path": "allowed", "content": "new"})]), response()],
                        extra=("--yield-after", "1"), expected=75)
        rows = self.records()
        rows[0]["config"]["capabilityPolicy"] = [[{"kind": "everything", "typo": True}]]
        journal = self.session / "journal.jsonl"
        journal.unlink()
        for row in rows:
            journal_append(journal, row)
        before = journal.read_bytes()
        self.cli("resume", self.session, "--json", expected=2)
        self.assertEqual(journal.read_bytes(), before)
        self.assertFalse((self.ws / "allowed").exists())


if __name__ == "__main__":
    unittest.main()
