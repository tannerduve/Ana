#!/usr/bin/env python3
"""Exercise the production harness with credential-free official-CLI stand-ins."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / ".lake/build/bin/harness"
SENTINEL = "never-forward-this-api-key"

FAKE_CLI = r'''#!/usr/bin/python3
import json, os, pathlib, sys, time
backend = pathlib.Path(sys.argv[0]).name
home = pathlib.Path(os.environ["HOME"])
plan = json.loads((home / (backend + "-plan.json")).read_text())
payload = json.load(sys.stdin)
trace = home / (backend + "-trace.jsonl")
index = len(trace.read_text().splitlines()) if trace.exists() else 0
with trace.open("a") as output:
    output.write(json.dumps({"args":sys.argv[1:], "cwd":os.getcwd(), "payload":payload,
                            "environment":dict(os.environ)}) + "\n")
entry = plan[min(index, len(plan)-1)]
if entry.get("sleep"):
    time.sleep(entry["sleep"])
if entry.get("error"):
    print("private CLI stderr: never-forward-this-api-key", file=sys.stderr)
    sys.exit(entry["error"])
if "raw" in entry:
    print(entry["raw"])
    sys.exit(0)
proposal = entry.get("proposal", {"text":"Finished.", "calls":[]})
if backend == "claude":
    output = {"type":"result", "subtype":"success", "is_error":False,
              "usage":{"input_tokens":20,"output_tokens":7,
                       "cache_read_input_tokens":3,"cache_creation_input_tokens":2}}
    if entry.get("structured", True): output["structured_output"] = proposal
    else: output["result"] = json.dumps(proposal)
    output.update(entry.get("override", {}))
    print(json.dumps(output))
else:
    events = [{"type":"thread.started","thread_id":"fixture-thread"}]
    if entry.get("startup_warning"):
        events += [{"type":"item.completed","item":{"type":"error", "message":"Optional feature unavailable"}}]
    events += [{"type":"turn.started"}]
    if entry.get("native_tool"):
        events += [{"type":"item.completed","item":{"type":"command_execution",
                     "command":"must not be admitted","status":"completed"}}]
    events += [{"type":"item.completed","item":{"type":"agent_message",
                "id":"final", "text":json.dumps(proposal)}}]
    if not entry.get("incomplete"):
        events += [{"type":"turn.completed",
                    "usage":{"input_tokens":25,"cached_input_tokens":5,"output_tokens":7}}]
    events += entry.get("extra_events", [])
    for event in events: print(json.dumps(event))
'''


def proposal(*calls, text=""):
    return {"text": text, "calls": [{"id": ident, "name": name, "input_json": json.dumps(args)}
                                   for ident, name, args in calls]}


class CLIProviders(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="harness-cli-provider-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.workspace = self.root / "workspace"
        self.workspace.mkdir()
        self.home = self.root / "home"
        self.home.mkdir()
        self.bin = self.root / "bin"
        self.bin.mkdir()
        for name in ["claude", "codex"]:
            path = self.bin / name
            path.write_text(FAKE_CLI)
            path.chmod(0o700)
        self.environment = {"PATH": str(self.bin) + ":" + os.defpath, "HOME": str(self.home),
                            "LANG": "C.UTF-8", "ANTHROPIC_API_KEY": SENTINEL,
                            "OPENAI_API_KEY": SENTINEL, "CODEX_API_KEY": SENTINEL,
                            "NODE_OPTIONS": "--require=/forbidden/preload.js",
                            "ANTHROPIC_BASE_URL": "https://forbidden.example"}
        self.config = {"model": "fixture-model", "commands": "deny", "maxModelAttempts": 8,
                       "maxToolCalls": 12, "maxResponseRepairs": 0, "operationTimeoutMs": 4000,
                       "maxElapsedMs": 15000}

    def prepare(self, backend, plan):
        name = "claude" if backend == "claude-code" else "codex"
        (self.home / (name + "-plan.json")).write_text(json.dumps(plan))
        self.config["modelBackend"] = backend
        config = self.root / (name + "-config.json")
        config.write_text(json.dumps(self.config))
        session = self.root / (name + "-session")
        args = [str(BINARY), "run", "--workspace", str(self.workspace), "--config", str(config),
                "--session", str(session), "--task", "Complete the requested work.", "--json"]
        return name, session, args

    def invoke(self, backend, plan, expected=0, extra=()):
        name, session, args = self.prepare(backend, plan)
        result = subprocess.run([*args, *extra], cwd=self.workspace, env=self.environment,
                                text=True, capture_output=True, timeout=20)
        self.assertEqual(result.returncode, expected, result.stderr + result.stdout)
        self.assertNotIn(SENTINEL, result.stdout + result.stderr)
        trace_path = self.home / (name + "-trace.jsonl")
        trace = [json.loads(line) for line in trace_path.read_text().splitlines()] if trace_path.exists() else []
        return session, result, trace

    def inspect(self, session):
        result = subprocess.run([str(BINARY), "inspect", str(session)], env=self.environment,
                                capture_output=True, text=True, timeout=10, check=True)
        return json.loads(result.stdout)["state"]

    def test_both_backends_read_edit_and_finish_through_real_engine(self):
        for backend in ["claude-code", "codex"]:
            with self.subTest(backend=backend):
                source = self.workspace / "calc.txt"
                source.write_text("2 + 2 = 5\n")
                digest = hashlib.sha256(source.read_bytes()).hexdigest()
                plan = [{"proposal": proposal(("read-1", "read", {"path": "calc.txt"}))},
                        {"proposal": proposal(("edit-1", "edit", {"path": "calc.txt", "old": "= 5", "new": "= 4", "expectedSha256": digest}))},
                        {"proposal": proposal(text="Corrected the arithmetic.")}]
                session, _, trace = self.invoke(backend, plan)
                self.assertEqual(source.read_text(), "2 + 2 = 4\n")
                state = self.inspect(session)
                self.assertEqual(state["modelAttempts"], 3)
                self.assertEqual(state["toolDispatches"], 2)
                self.assertEqual(state["knownInputTokens"], 75)
                self.assertEqual(state["knownOutputTokens"], 21)
                self.assertEqual(state["config"]["modelBackend"], backend)
                self.assertIn(digest, json.dumps(trace[1]["payload"]))
                for item in trace:
                    self.assertNotEqual(Path(item["cwd"]), self.workspace)
                    self.assertNotEqual(Path(item["cwd"]), session)
                    self.assertFalse(Path(item["cwd"]).exists(), "CLI scratch was retained")
                    self.assertTrue(item["payload"]["request"]["tools"])
                    self.assertNotIn(SENTINEL, json.dumps(item["environment"]))
                    self.assertNotIn("NODE_OPTIONS", item["environment"])
                    self.assertNotIn("ANTHROPIC_BASE_URL", item["environment"])
                if backend == "claude-code":
                    args = trace[0]["args"]
                    self.assertEqual(args[args.index("--tools")+1], "")
                    self.assertIn("--safe-mode", args)
                    self.assertIn("--no-session-persistence", args)
                    self.assertNotIn("--bare", args, "bare mode disables subscription authentication")
                else:
                    args = trace[0]["args"]
                    self.assertEqual(args[args.index("--sandbox")+1], "read-only")
                    self.assertIn("--ignore-user-config", args)
                    self.assertIn('forced_login_method="chatgpt"', args)
                    self.assertIn("shell_tool", args)
                count = len(trace)
                for command in ["replay", "resume"]:
                    subprocess.run([str(BINARY), command, str(session)], env=self.environment,
                                   capture_output=True, timeout=10, check=True)
                name = "claude" if backend == "claude-code" else "codex"
                self.assertEqual(len((self.home / (name+"-trace.jsonl")).read_text().splitlines()), count)

    def test_domain_application_and_policy_remain_authoritative(self):
        self.config["toolPolicy"] = "deny"
        for backend in ["claude-code", "codex"]:
            session, _, _ = self.invoke(backend, [
                {"proposal": proposal(("create-1", "create", {"path":"forbidden", "content":"bad"}))},
                {"proposal": proposal(text="The operation was denied.")}])
            self.assertFalse((self.workspace / "forbidden").exists())
            self.assertEqual(self.inspect(session)["toolDispatches"], 0)

    def test_invalid_later_proposal_prevents_earlier_write(self):
        for backend in ["claude-code", "codex"]:
            session, _, _ = self.invoke(backend, [{"proposal": proposal(
                ("first", "create", {"path":"forbidden", "content":"bad"}),
                ("second", "nonexistent", {}))}], expected=1)
            self.assertFalse((self.workspace / "forbidden").exists())
            self.assertEqual(self.inspect(session)["toolDispatches"], 0)

    def test_unknown_backend_is_rejected_before_launch(self):
        _, result, trace = self.invoke("unknown", [{}], expected=2)
        self.assertIn("modelBackend must be", result.stderr)
        self.assertEqual(trace, [])

    def test_malformed_output_admits_no_tools(self):
        for backend in ["claude-code", "codex"]:
            session, _, _ = self.invoke(backend, [{"raw":"not JSON"}], expected=1)
            self.assertEqual(self.inspect(session)["toolDispatches"], 0)

    def test_cli_failure_does_not_expose_stderr_or_credentials(self):
        for backend in ["claude-code", "codex"]:
            _, result, _ = self.invoke(backend, [{"error":1}], expected=1)
            self.assertIn("check CLI login", result.stdout)
            self.assertNotIn("private CLI stderr", result.stdout + result.stderr)

    def test_claude_plain_result_envelope(self):
        self.invoke("claude-code", [{"structured":False}])

    def test_claude_null_structured_result_uses_final_text(self):
        self.invoke("claude-code", [{"structured":False, "override":{"structured_output":None}}])

    def test_claude_error_result_cannot_supply_proposals(self):
        session, _, _ = self.invoke("claude-code", [{"override":{"is_error":True}}], expected=1)
        self.assertEqual(self.inspect(session)["toolDispatches"], 0)

    def test_codex_incomplete_stream_cannot_supply_proposals(self):
        session, _, _ = self.invoke("codex", [{"incomplete":True}], expected=1)
        self.assertEqual(self.inspect(session)["toolDispatches"], 0)

    def test_codex_native_tool_activity_is_rejected(self):
        session, _, _ = self.invoke("codex", [{"native_tool":True}], expected=1)
        self.assertEqual(self.inspect(session)["toolDispatches"], 0)

    def test_codex_repeated_terminal_is_rejected(self):
        session, _, _ = self.invoke("codex", [{"extra_events":[{"type":"turn.completed"}]}], expected=1)
        self.assertEqual(self.inspect(session)["toolDispatches"], 0)

    def test_codex_startup_diagnostic_requires_later_successful_turn(self):
        self.invoke("codex", [{"startup_warning":True}])

    def test_default_model_uses_cli_default(self):
        self.config["model"] = "default"
        for backend in ["claude-code", "codex"]:
            _, _, trace = self.invoke(backend, [{}])
            self.assertNotIn("--model", trace[0]["args"])

    def test_cli_installation_inside_model_workspace_is_refused(self):
        unsafe_bin = self.workspace / "bin"
        unsafe_bin.mkdir()
        for name in ["claude", "codex"]:
            path = unsafe_bin / name
            path.write_text(FAKE_CLI)
            path.chmod(0o700)
        self.environment["PATH"] = str(unsafe_bin) + ":" + self.environment["PATH"]
        for backend in ["claude-code", "codex"]:
            _, result, trace = self.invoke(backend, [{}], expected=1)
            self.assertIn("outside the workspace", result.stdout)
            self.assertEqual(trace, [])

    def test_response_byte_limit_refuses_truncated_proposals(self):
        self.config["maxResponseBytes"] = 100
        for backend in ["claude-code", "codex"]:
            session, _, _ = self.invoke(backend, [{"proposal":proposal(
                ("create-1", "create", {"path":"forbidden", "content":"bad"}))}], expected=1)
            self.assertFalse((self.workspace / "forbidden").exists())
            self.assertEqual(self.inspect(session)["toolDispatches"], 0)

    def test_model_workspace_cannot_be_cli_scratch_root(self):
        self.environment["TMPDIR"] = str(self.workspace)
        for backend in ["claude-code", "codex"]:
            _, result, trace = self.invoke(backend, [{}], expected=1)
            self.assertIn("change TMPDIR", result.stdout)
            self.assertEqual(trace, [])

    def test_inventory_receives_only_its_tools_and_returns_typed_results(self):
        self.config.pop("commands")
        for backend in ["claude-code", "codex"]:
            name, session, args = self.prepare(backend, [
                {"proposal":proposal(("lookup-1", "lookup", {"sku":"N-CABLE"}))},
                {"proposal":proposal(text="Found the item.")}])
            index = args.index("--workspace")
            del args[index:index+2]
            args += ["--application", "inventory", "--data", str(ROOT / "examples/inventory/stock.json")]
            result = subprocess.run(args, env=self.environment, text=True, capture_output=True, timeout=15)
            self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
            trace = [json.loads(line) for line in (self.home / (name+"-trace.jsonl")).read_text().splitlines()]
            self.assertEqual({tool["name"] for tool in trace[0]["payload"]["request"]["tools"]},
                             {"lookup", "reserve", "warehouse_totals", "low_stock"})
            self.assertIn('N-CABLE', json.dumps(trace[1]["payload"]))
            self.assertEqual(self.inspect(session)["toolDispatches"], 1)

    def test_compaction_uses_same_cli_backend_without_advertising_tools(self):
        self.config.update({"maxContextBytes":40000, "compactAtPercent":1,
                            "compactionKeepMessages":2})
        for backend in ["claude-code", "codex"]:
            session, _, trace = self.invoke(backend, [
                {"proposal":proposal(("read-1", "read", {"path":"missing.txt"}))},
                {"proposal":proposal(text="The task is to complete the requested work.")},
                {"proposal":proposal(text="Complete.")}])
            summaries = [item for item in trace if item["payload"]["request"]["purpose"] == "summary"]
            self.assertEqual(len(summaries), 1)
            self.assertEqual(summaries[0]["payload"]["request"]["tools"], [])
            self.assertEqual(self.inspect(session)["modelAttempts"], 3)

    def test_yield_resume_and_followup_preserve_backend_and_budget(self):
        for backend in ["claude-code", "codex"]:
            session, _, _ = self.invoke(backend, [
                {"proposal": proposal(("read-1", "read", {"path":"missing.txt"}))},
                {"proposal": proposal(text="No file found.")},
                {"proposal": proposal(text="Follow-up complete.")}], expected=75,
                extra=["--yield-after", "2"])
            for arguments in [["resume", str(session)], ["continue", str(session), "--task", "Explain."]]:
                result = subprocess.run([str(BINARY), *arguments], env=self.environment,
                                        text=True, capture_output=True, timeout=15)
                self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
            state = self.inspect(session)
            self.assertEqual(state["config"]["modelBackend"], backend)
            self.assertEqual(state["modelAttempts"], 3)
            self.assertEqual(state["toolDispatches"], 1)

    def test_cancellation_settles_cli_without_admitting_output(self):
        for backend in ["claude-code", "codex"]:
            name, session, args = self.prepare(backend, [{"sleep":10}])
            process = subprocess.Popen(args, env=self.environment, stdout=subprocess.PIPE,
                                       stderr=subprocess.PIPE, text=True)
            try:
                trace = self.home / (name+"-trace.jsonl")
                deadline = time.monotonic() + 5
                while not trace.exists() and time.monotonic() < deadline:
                    time.sleep(0.02)
                self.assertTrue(trace.exists(), "CLI never started")
                subprocess.run([str(BINARY), "cancel", str(session)], env=self.environment,
                               capture_output=True, timeout=5, check=True)
                stdout, stderr = process.communicate(timeout=8)
                self.assertNotEqual(process.returncode, 0, stdout + stderr)
                self.assertEqual(self.inspect(session)["toolDispatches"], 0)
            finally:
                if process.poll() is None:
                    process.kill()
                    process.communicate()


if __name__ == "__main__":
    unittest.main()
