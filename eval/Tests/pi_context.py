"""Local offline gate: pinned Node/installed Pi SDK, fake HTTP, no Docker or Lean build."""
import http.server
import json
import math
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "runner"))
import public_bench as public
import sustained
from paths import evaluation_provenance, node_identity

SETTINGS = {"piContextWindow": 32768,
            "piCompaction": {"enabled": True, "reserveTokens": 8192, "keepRecentTokens": 8192}}


class PiContext(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.node = node_identity()["binary"]
        if not (ROOT / "baseline/node_modules/@earendil-works/pi-coding-agent/package.json").is_file():
            raise RuntimeError("install pinned baseline dependencies with npm ci --prefix baseline --ignore-scripts")

    def environment(self, directory):
        home = directory / "home"
        home.mkdir(exist_ok=True)
        return {"PATH": str(Path(self.node).parent) + ":/usr/bin:/bin", "HOME": str(home),
                "LANG": "C.UTF-8", "TMPDIR": str(directory), "NO_PROXY": "127.0.0.1",
                "PI_SKIP_VERSION_CHECK": "1"}

    def test_mode_validation_rejects_types_unknown_keys_and_impossible_bounds(self):
        invalid = [None, [], {"unknown": 1}, {"piContextWindow": True}, {"piContextWindow": "32768"},
                   {"piContextWindow": 0}, {"piContextWindow": -1}, {"piContextWindow": 1.5},
                   {"piContextWindow": 2**53}, {"piCompaction": None}, {"piCompaction": []},
                   {"piCompaction": {"enabled": 1}}, {"piCompaction": {"reserveTokens": True}},
                   {"piCompaction": {"keepRecentTokens": -1}}, {"piCompaction": {"modelOverrides": {}}},
                   {"piContextWindow": 100, "piCompaction": {"enabled": False, "reserveTokens": 100}},
                   {"piContextWindow": 100, "piCompaction": {"reserveTokens": 50, "keepRecentTokens": 50}}]
        for value in invalid:
            with self.subTest(value=value), self.assertRaises(ValueError):
                public.validate_pi_settings(value)
        with self.assertRaises(ValueError):
            public.validate_pi_settings(SETTINGS, "lean")
        self.assertEqual(public.validate_pi_settings({}), {})
        copied = public.validate_pi_settings(SETTINGS)
        copied["piCompaction"]["enabled"] = False
        self.assertTrue(SETTINGS["piCompaction"]["enabled"])
        self.assertIn("baseline/context-settings.mjs", evaluation_provenance()["evaluation_sources_sha256"])

    def test_pinned_sdk_defaults_and_explicit_options_and_offline_preflight(self):
        code = """
          import {getModel} from '@earendil-works/pi-ai/compat';
          import {SettingsManager} from '@earendil-works/pi-coding-agent';
          import {piContextOptions} from './context-settings.mjs';
          const base=getModel('anthropic','claude-opus-5-5');
          const defaults=SettingsManager.inMemory().getCompactionSettings(base);
          const cases=JSON.parse(process.argv[1]);
          console.log(JSON.stringify(cases.map(config=>{
            try {
              const options=piContextOptions(config,base,defaults);
              const model={...base,...options.modelOverrides};
              const settings=SettingsManager.inMemory(options.settingsOverrides).getCompactionSettings(model);
              return {options,contextWindow:model.contextWindow,settings,defaults,catalog:base.contextWindow};
            } catch(error) { return {error:error.message}; }
          })));
        """
        cases = [{"track": "product", "maxOutputTokens": 4096},
                 {"track": "product", "maxOutputTokens": 4096, **SETTINGS},
                 {"track": "controlled", "maxOutputTokens": 4096, **SETTINGS},
                 {"track": "product", "maxOutputTokens": 4096, "piContextWindow": 2**52},
                 {"track": "product", "maxOutputTokens": 4096, "piContextWindow": 32768},
                 {"track": "product", "maxOutputTokens": 4096, "piContextWindow": 4096},
                 {"track": "product", "maxOutputTokens": 4096, "piContextWindow": True},
                 {"track": "product", "maxOutputTokens": 4096, "piContextWindow": 32768.5},
                 {"track": "product", "maxOutputTokens": 4096, "piCompaction": {"enabled": "yes"}},
                 {"track": "product", "maxOutputTokens": 4096, "piCompaction": {"surprise": 1}},
                 {"track": "product", "maxOutputTokens": 4096, "piCompaction": {"reserveTokens": True}},
                 {"track": "product", "maxOutputTokens": 4096, "piCompaction": {"keepRecentTokens": -1}},
                 {"track": "product", "maxOutputTokens": 4096, "piContextWindow": 32768,
                  "piCompaction": {"enabled": False, "reserveTokens": 32768}},
                 {"track": "product", "maxOutputTokens": 4096, "piUnexpected": 1},
                 {"track": "product", "maxOutputTokens": 4096, "piContextWindow": 65536}]
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            result = subprocess.run([self.node, "--input-type=module", "-e", code, json.dumps(cases)],
                cwd=ROOT / "baseline", env=self.environment(directory), capture_output=True, text=True, timeout=30)
            self.assertEqual(result.returncode, 0, result.stderr)
            actual = json.loads(result.stdout)
            self.assertEqual(actual[0]["options"], {"modelOverrides": {}, "settingsOverrides": {}, "record": None})
            self.assertEqual(actual[0]["settings"], actual[0]["defaults"])
            self.assertEqual(actual[0]["contextWindow"], actual[0]["catalog"])
            self.assertEqual(actual[1]["contextWindow"], 32768)
            self.assertEqual(actual[1]["settings"], SETTINGS["piCompaction"])
            self.assertTrue(all("error" in row for row in actual[2:-1]))
            self.assertEqual(actual[-1]["contextWindow"], 65536)
            self.assertEqual(actual[-1]["settings"], actual[-1]["defaults"])
            for row in [actual[1], actual[-1]]:
                self.assertEqual(row["options"]["record"]["effective"]["compaction"], row["settings"])
            workspace = directory / "workspace"; workspace.mkdir()
            for index, config in enumerate([None, cases[1], cases[4]]):
                command = [self.node, str(ROOT / "baseline/preflight.mjs"), "claude-opus-5-5",
                           str(workspace), str(directory / f"sessions-{index}")]
                if config is not None:
                    config_path = directory / f"config-{index}.json"
                    config_path.write_text(json.dumps(config)); command.append(str(config_path))
                preflight = subprocess.run(command, env=self.environment(directory), capture_output=True, text=True, timeout=30)
                if index == 2:
                    self.assertNotEqual(preflight.returncode, 0)
                    self.assertIn("leave room", preflight.stderr)
                else:
                    self.assertEqual(preflight.returncode, 0, preflight.stderr)
                    self.assertEqual(json.loads(preflight.stdout)["providerRequests"], 0)

    def test_actual_wrapper_compacts_only_with_explicit_bounded_settings(self):
        for bounded in [False, True]:
            with self.subTest(bounded=bounded), tempfile.TemporaryDirectory() as tmp:
                directory = Path(tmp); workspace = directory / "workspace"; workspace.mkdir()
                sessions = directory / "sessions"; sessions.mkdir()
                for n in range(1, 9):
                    (workspace / f"file{n}.txt").write_text("".join(
                        f"{i:04} fixture{n}: diagnostic source line keeps deterministic searchable content. "
                        + "x" * 30 + "\n" for i in range(220)))
                requests = []; task_count = 0
                class Provider(http.server.BaseHTTPRequestHandler):
                    def log_message(self, *_): pass
                    def do_POST(self):
                        nonlocal task_count
                        length = int(self.headers["Content-Length"])
                        payload = json.loads(self.rfile.read(length)); summary = not payload.get("tools")
                        requests.append({"summary": summary, "bytes": length, "max_tokens": payload.get("max_tokens")})
                        if length > 144000:
                            body = b'{"type":"error","error":{"type":"invalid_request_error","message":"fixture wire ceiling"}}'
                            self.send_response(400); self.send_header("Content-Length", str(len(body)))
                            self.end_headers(); self.wfile.write(body); return
                        if summary:
                            block = {"type": "text", "text": "Continue reading remaining numbered fixture files; no edits."}
                        else:
                            task_count += 1
                            block = ({"type": "tool_use", "id": f"read-{task_count}", "name": "read",
                                      "input": {"path": f"file{task_count}.txt"}} if task_count <= 8
                                     else {"type": "text", "text": "All eight reads finished."})
                        tool = block["type"] == "tool_use"
                        initial = {**block, "input": {}} if tool else {"type": "text", "text": ""}
                        delta = ({"type": "input_json_delta", "partial_json": json.dumps(block["input"])} if tool
                                 else {"type": "text_delta", "text": block["text"]})
                        events = [{"type": "message_start", "message": {"id": f"msg-{len(requests)}", "type": "message",
                            "role": "assistant", "model": "claude-opus-5-5", "content": [], "stop_reason": None,
                            "stop_sequence": None, "usage": {"input_tokens": math.ceil(length / 3.5), "output_tokens": 0}}},
                            {"type": "content_block_start", "index": 0, "content_block": initial},
                            {"type": "content_block_delta", "index": 0, "delta": delta},
                            {"type": "content_block_stop", "index": 0},
                            {"type": "message_delta", "delta": {"stop_reason": "tool_use" if tool else "end_turn",
                             "stop_sequence": None}, "usage": {"output_tokens": 10}}, {"type": "message_stop"}]
                        body = b"".join(("event: " + e["type"] + "\ndata: " + json.dumps(e) + "\n\n").encode() for e in events)
                        self.send_response(200); self.send_header("Content-Type", "text/event-stream")
                        self.send_header("Content-Length", str(len(body))); self.end_headers(); self.wfile.write(body)
                server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Provider)
                thread = threading.Thread(target=server.serve_forever, daemon=True); thread.start()
                config = {"model": "claude-opus-5-5", "track": "product", "workspace": str(workspace),
                    "sessionDir": str(sessions), "testEndpoint": f"http://127.0.0.1:{server.server_port}/v1/messages",
                    "maxOutputTokens": 4096, "maxToolCalls": 12, "operationTimeoutMs": 10000, "maxElapsedMs": 30000,
                    "maxContextBytes": 120000, "task": "Read file1.txt through file8.txt in order, then answer. No edits."}
                if bounded: config.update(SETTINGS)
                path = directory / "config.json"; path.write_text(json.dumps(config))
                try:
                    result = subprocess.run([self.node, str(ROOT / "baseline/run.mjs"), str(path)],
                        env=self.environment(directory), capture_output=True, text=True, timeout=40)
                finally:
                    server.shutdown(); server.server_close(); thread.join()
                events = [json.loads(line) for line in result.stdout.splitlines()]
                terminal = next(e for e in reversed(events) if e.get("type") == "evaluation_end")
                compactions = [json.loads(line) for p in (sessions / "pi").glob("*.jsonl")
                               for line in p.read_text().split("\n") if line and json.loads(line).get("type") == "compaction"]
                print(json.dumps({"fixture": "bounded" if bounded else "unset",
                    "provider_requests": len(requests), "summary_requests": sum(r["summary"] for r in requests),
                    "native_compactions": len(compactions), "maximum_request_bytes": max(r["bytes"] for r in requests),
                    "exit_code": result.returncode}))
                self.assertTrue(all(r["max_tokens"] == 4096 for r in requests))
                if bounded:
                    self.assertEqual(result.returncode, 0, result.stderr + result.stdout[-1000:])
                    self.assertEqual(task_count, 9)
                    self.assertGreaterEqual(len(compactions), 2)
                    self.assertTrue(all(r["bytes"] <= 144000 for r in requests))
                    self.assertEqual(terminal["piContextConfiguration"]["requested"], SETTINGS)
                    self.assertEqual(terminal["piContextConfiguration"]["effective"]["compaction"], SETTINGS["piCompaction"])
                else:
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(compactions, [])
                    self.assertGreater(requests[-1]["bytes"], 144000)
                    self.assertNotIn("piContextConfiguration", terminal)

    def test_configuration_recording_and_manifest_plumbing(self):
        # Configuration is written by the real run_one before mocked preparation;
        # no container, provider registration or candidate invocation occurs.
        for options in [{}, SETTINGS]:
            with self.subTest(options=options), tempfile.TemporaryDirectory() as tmp:
                directory = Path(tmp); broker = Mock(records=[])
                args = SimpleNamespace(model="claude-opus-5-5", max_attempts=2, max_tools=2, context_bytes=30000,
                    timeout=10, prepared_bwrap=None, harness_root=ROOT.parent, cohort="fixture", attempt=1,
                    apt_https=False, apt_main_only=False, pi_settings=options)
                with patch.object(public, "harness_binary", return_value=directory / "harness"), \
                     patch.object(public, "eval_tools_binary", return_value=directory / "tools"), \
                     patch.object(public, "assert_space", side_effect=RuntimeError("offline boundary")):
                    record = public.run_one({"id": "fixture", "benchmark": "fixture", "repository_task": True,
                        "workspace": "/workspace",
                        "image_digest": "fixture"}, "pi", 0, [], args, directory, broker, task_text="task")
                config = json.loads((directory / record["run_id"] / "pi-config.json").read_text())
                self.assertEqual({k: config[k] for k in SETTINGS if k in config}, options)
                self.assertEqual(record.get("pi_context_settings", {}), options)
                self.assertFalse(broker.add_run.called)
                events = directory / "events.jsonl"
                events.write_text(json.dumps({"type": "evaluation_end", "toolDispatches": 0,
                    "piContextConfiguration": {"requested": options, "effective": {"contextWindow": 32768}}}) + "\n")
                self.assertEqual(public.pi_terminal_observation(events)["pi_context_configuration"]["requested"], options)
        manifest = {"schema_version": 1, "tasks": [], "modes": [{"id": "pi", "engine": "pi",
            "max_attempts": 40, "max_tools": 120, "context_bytes": 120000, "timeout": 900, "pi": SETTINGS}]}
        self.assertEqual(sustained.validate_manifest(manifest)["modes"][0]["pi"], SETTINGS)
        manifest["modes"][0]["engine"] = "lean"
        with self.assertRaises(ValueError): sustained.validate_manifest(manifest)
        from plan_context_version import run_fixture
        with tempfile.TemporaryDirectory() as tmp:
            observed = run_fixture("sustained", Path(tmp), [], pi_settings=SETTINGS)
            self.assertEqual(observed["plan"]["modes"][0]["pi"], SETTINGS)
            self.assertEqual(observed["child_pi_settings"], SETTINGS)
            self.assertEqual(observed["child_engine"], "pi")


if __name__ == "__main__": unittest.main()
