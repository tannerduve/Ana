"""Unpaid request evidence: actual wire bytes, admission faults and audit controls."""
import copy
from contextlib import contextmanager
from decimal import Decimal
import hashlib
import http.client
import http.server
import json
from pathlib import Path
import sys
import tempfile
import threading
import unittest
from unittest.mock import patch
import urllib.error
import urllib.request

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "runner"))
import broker as module
from request_evidence import (AuditError, audit_request_evidence, context_digest,
                              outbound_evidence, parse_request, user_text_digests, audit_initial_task)
from patch_review import automated_checks


@contextmanager
def fixture():
    captured = []
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        class Provider(http.server.BaseHTTPRequestHandler):
            def log_message(self, *_): pass
            def do_POST(self):
                raw = self.rfile.read(int(self.headers["Content-Length"]))
                # Independently read durable evidence BEFORE sending any response.
                captured.append((raw, json.loads((directory / "broker.json").read_text())))
                body = b'{"usage":{"input_tokens":3,"output_tokens":2}}'
                self.send_response(200)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
        server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Provider)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            with module.Broker("private-test-key", directory,
                    upstream=f"http://127.0.0.1:{server.server_port}") as relay:
                yield relay, relay.add_run("fixture"), captured, directory
        finally:
            server.shutdown(); server.server_close(); thread.join()


def send(endpoint, raw):
    with urllib.request.urlopen(urllib.request.Request(endpoint, data=raw), timeout=5) as response:
        return response.read()


def body():
    return (b'{ "model":"claude-opus-5-5","max_tokens":4096,"system":"private-instructions",'
            b'"messages":[{"role":"assistant","content":['
            b'{"type":"thinking","thinking":"opaque","signature":"private-signature"},'
            b'{"type":"tool_use","id":"id","name":"read","input":'
            b'{"path":"\xc3\xa9\\t.txt","exact":1.00000000000000001}}]}]}')


class WireEvidence(unittest.TestCase):
    def test_actual_upstream_bytes_match_preexisting_durable_evidence(self):
        with fixture() as (relay, endpoint, captured, directory):
            raw = body()
            send(endpoint, raw)
            relay.close_run("fixture")
            self.assertEqual(len(captured), 1)
            received, durable = captured[0]
            record = durable["records"][0]
            self.assertEqual(received, raw)
            self.assertEqual(record["outbound_body_sha256"], hashlib.sha256(received).hexdigest())
            self.assertEqual(record["outbound_body_bytes"], len(received))
            self.assertEqual(record["system_messages_sha256"], context_digest(parse_request(received)))
            self.assertEqual(record["outbound_transport_state"], "dispatch_intent")
            self.assertTrue(record["active"])
            self.assertFalse(record["accounting_settled"])
            self.assertEqual(relay.records[0]["outbound_transport_state"], "response_observed")
            saved = (directory / "broker.json").read_text()
            for secret in ("private-test-key", "private-instructions", "private-signature", "x-api-key"):
                self.assertNotIn(secret, saved)
            self.assertFalse((directory / "request-evidence").exists())

    def test_settings_are_durable_before_forward_and_preserve_wire_bytes(self):
        payload = {
            "model": "claude-opus-5-5", "max_tokens": 4096,
            "thinking": {"type": "adaptive"},
            "output_config": {"effort": "low"},
            "messages": [
                {"role": "user", "content": "private prompt"},
                {"role": "system", "content": [], "output_config": {"effort": "high"}},
            ],
        }
        raw = json.dumps(payload).encode()
        with fixture() as (relay, endpoint, captured, directory):
            send(endpoint, raw)
            relay.close_run("fixture")
            received, before_response = captured[0]
            settings = before_response["records"][0]["request_settings"]
            self.assertEqual(received, raw)
            self.assertEqual(settings["top_level_effort"], {"state": "known", "value": "low"})
            self.assertEqual(settings["system_message_efforts"], [
                {"message_index": 1, "effort": {"state": "known", "value": "high"}},
            ])
            self.assertEqual(settings["max_tokens"], {"state": "known", "value": 4096})
            saved = json.loads((directory / "broker.json").read_text())
            self.assertEqual(saved["records"][0]["request_settings"], settings)
            self.assertTrue(saved["records"][0]["accounting_settled"])
            self.assertNotIn("private prompt", json.dumps(settings))

    def test_initial_user_text_positions_are_durable_only_on_first_attempt(self):
        task = "Implement the task. Do not weaken unrelated tests."
        payload = {"model": "claude-opus-5-5", "max_tokens": 4096,
                   "messages": [{"role": "user", "content": "budget notice"},
                                {"role": "user", "content": [{"type": "text", "text": task}]}]}
        with fixture() as (relay, endpoint, captured, _):
            for _ in range(2): send(endpoint, json.dumps(payload).encode())
            relay.close_run("fixture")
            recorded = captured[0][1]["records"][0]["initial_user_text_sha256"]
            self.assertEqual(recorded, user_text_digests(payload))
            self.assertNotIn("initial_user_text_sha256", relay.records[1])
            matched = audit_initial_task(relay.records, hashlib.sha256(task.encode()).hexdigest())
            self.assertEqual(matched["matching_positions"][0]["message_index"], 1)

    def test_pre_forward_storage_failure_never_dispatches_or_loses_reservation(self):
        with fixture() as (relay, endpoint, captured, directory):
            original, failed = relay._save, False
            def fail_once():
                nonlocal failed
                if relay.records and not failed:
                    failed = True
                    raise OSError("injected pre-forward evidence failure")
                original()
            with patch.object(relay, "_save", side_effect=fail_once):
                with self.assertRaises((http.client.RemoteDisconnected, urllib.error.URLError)):
                    send(endpoint, body())
                with self.assertRaisesRegex(RuntimeError, "storage failed"):
                    relay.close_run("fixture")
            self.assertEqual(captured, [])
            self.assertEqual(len(relay.records), 1)
            row = relay.records[0]
            self.assertEqual(row["outbound_transport_state"], "not_started")
            self.assertFalse(row["accounting_settled"])
            self.assertEqual(row["charged_usd"], row["reserved_usd"])
            self.assertEqual(relay.total, row["reserved_usd"])
            self.assertIsNotNone(json.loads((directory / "broker.json").read_text())["storage_failure"])
            endpoint2 = relay.add_run("later")
            with self.assertRaises(urllib.error.HTTPError): send(endpoint2, body())
            self.assertEqual(len(relay.records), 1)
            self.assertEqual(captured, [])

    def test_ambiguous_body_refuses_before_reservation_and_stops_later_admission(self):
        with fixture() as (relay, endpoint, captured, directory):
            with self.assertRaises(urllib.error.HTTPError) as failure:
                send(endpoint, b'{"messages":[],"messages":[]}')
            self.assertEqual(failure.exception.code, 400)
            self.assertEqual(relay.records, [])
            self.assertEqual(relay.total, 0)
            self.assertEqual(relay.admission_refusal("fixture")["kind"], "request_evidence")
            with self.assertRaises(urllib.error.HTTPError): send(endpoint, body())
            with self.assertRaisesRegex(RuntimeError, "request evidence"):
                relay.close_run("fixture")
            self.assertEqual(captured, [])
            self.assertIsNotNone(json.loads((directory / "broker.json").read_text())["request_evidence_failure"])


class CanonicalEvidence(unittest.TestCase):
    def test_first_task_requires_whole_unchanged_text_and_observed_response(self):
        task = "Task\n\nDo not disable unrelated tests."
        expected = hashlib.sha256(task.encode()).hexdigest()
        def row(content):
            payload = {"messages": [{"role": "user", "content": content}]}
            raw = json.dumps(payload).encode()
            return {**outbound_evidence(raw)[1], "attempt": 1, "request_bytes": len(raw),
                    "outbound_transport_state": "response_observed",
                    "initial_user_text_sha256": user_text_digests(payload)}
        for content in [task, [{"type": "text", "text": task}]]:
            self.assertTrue(audit_initial_task([row(content)], expected)["passed"])
        for content in [task.replace("Do not disable", "Disable"),
                        [{"type": "text", "text": "Task\n\n"},
                         {"type": "text", "text": "Do not disable unrelated tests."}],
                        [{"type": "tool_result", "tool_use_id": "x", "content": task}]]:
            with self.assertRaisesRegex(AuditError, "absent or altered"):
                audit_initial_task([row(content)], expected)
        for broken in [{key: value for key, value in row(task).items() if key != "initial_user_text_sha256"},
                       {**row(task), "outbound_transport_state": "not_started"},
                       {**row(task), "outbound_transport_state": "dispatch_intent"}]:
            with self.assertRaises(AuditError): audit_initial_task([broken], expected)
        with self.assertRaisesRegex(AuditError, "absent or altered"):
            audit_initial_task([row("wrong first task"), {**row(task), "attempt": 2}], expected)
        legacy = automated_checks({})
        self.assertNotIn("initial_task_request", legacy)
        self.assertFalse(automated_checks({"request_evidence_version": 1})["initial_task_request"])
        self.assertTrue(automated_checks({"request_evidence_version": 1,
            "initial_task_request_evidence": audit_initial_task([row(task)], expected)})["initial_task_request"])

    def test_spelling_normalization_preserves_exact_wire_digest(self):
        first = b'{"system":"\xc3\xa9\\t","messages":[1.0,{"b":true,"a":null}]}'
        second = b'{ "messages": [1e0,{"a":null,"b":true}], "system":"\\u00e9\\u0009" }'
        _, a = outbound_evidence(first)
        _, b = outbound_evidence(second)
        self.assertEqual(a["system_messages_sha256"], b["system_messages_sha256"])
        self.assertNotEqual(a["outbound_body_sha256"], b["outbound_body_sha256"])
        for left, right in [(1, "1"), (1, True), (Decimal("1.00000000000000001"), 1),
                            ("é", "e\u0301"), ([1, 2], [2, 1])]:
            self.assertNotEqual(context_digest({"messages": left}), context_digest({"messages": right}))
        self.assertNotEqual(context_digest({"messages": []}), context_digest({"system": None, "messages": []}))

    def test_bounds_and_ambiguities_are_explicit(self):
        for raw in [b'{"messages":[],"\\u006dessages":[]}', b'{"system":"\\ud800"}',
                    b'{"system":"\xff"}', b'{"messages":[NaN]}', b'{"messages":[1e4097]}',
                    b'{"messages":[1e-4097]}', b'{"messages":[0e-20]}',
                    b'{"messages":'+b'1'*4097+b'}',
                    b'{"messages":['+b','.join([b'1e4096']*257)+b']}',
                    b'{"messages":'+b'['*128+b'0'+b']'*128+b'}']:
            with self.subTest(raw=raw[:60]), self.assertRaises((AuditError, ValueError, UnicodeError)):
                outbound_evidence(raw)
        for raw in [b'{"messages":[1e4096,1e-4096]}', b'{"messages":'+b'1'*4096+b'}',
                    b'{"messages":'+b'['*127+b'0'+b']'*127+b'}',
                    b'{"system":"1e9999999999 [[[[ \\" still text"}']:
            outbound_evidence(raw)

    def test_context_mutations_and_missing_evidence_fail_closed(self):
        request, evidence = outbound_evidence(body())
        charge = {**evidence, "attempt": 1, "request_bytes": len(body())}
        self.assertEqual(audit_request_evidence([request], [charge], required_version=1)["status"], "matched")
        variants = []
        changed = copy.deepcopy(request); changed["system"] += " altered"; variants.append(changed)
        changed = copy.deepcopy(request); changed["messages"][0]["content"].reverse(); variants.append(changed)
        changed = copy.deepcopy(request); changed["messages"][0]["content"][0]["signature"] += "x"; variants.append(changed)
        changed = copy.deepcopy(request); changed["messages"][0]["content"][1]["input"]["exact"] = 1; variants.append(changed)
        for changed in variants:
            with self.assertRaisesRegex(AuditError, "system/messages differ"):
                audit_request_evidence([changed], [charge], required_version=1)
        for damaged in [{}, {**charge, "system_messages_sha256": None},
                        {**charge, "attempt": 2}, {**charge, "request_evidence_version": True},
                        {**charge, "outbound_body_bytes": 1}]:
            with self.assertRaises(AuditError): audit_request_evidence([request], [damaged], required_version=1)
        with self.assertRaises(AuditError): audit_request_evidence([request], [], required_version=1)
        with self.assertRaises(AuditError): audit_request_evidence([request], [charge], required_version=2)
        self.assertEqual(audit_request_evidence([request], [{}])["status"], "unavailable_legacy")


class SettingsEvidence(unittest.TestCase):
    def evidence(self, **extra):
        payload = {"model": "fixture", "max_tokens": 4096,
                   "system": "private instructions", "messages": []}
        payload.update(extra)
        decoded, evidence = outbound_evidence(json.dumps(payload).encode())
        self.assertEqual(decoded, payload)
        return payload, evidence

    def test_distinct_top_level_and_message_effort(self):
        _, evidence = self.evidence(
            thinking={"type": "adaptive"}, output_config={"effort": "low"},
            messages=[{"role": "user", "content": "private content"},
                      {"role": "system", "content": [], "output_config": {"effort": "high"}}])
        settings = evidence["request_settings"]
        self.assertEqual(settings["version"], 1)
        self.assertEqual(settings["thinking_type"], {"state": "known", "value": "adaptive"})
        self.assertEqual(settings["top_level_effort"], {"state": "known", "value": "low"})
        self.assertEqual(settings["system_message_efforts"], [
            {"message_index": 1, "effort": {"state": "known", "value": "high"}},
        ])
        self.assertNotIn("private content", json.dumps(settings))

    def test_absent_null_and_invalid_values_remain_distinct(self):
        _, evidence = self.evidence()
        self.assertEqual(evidence["request_settings"]["top_level_effort"]["state"], "absent")
        _, evidence = self.evidence(output_config=None, thinking=[], max_tokens=True)
        settings = evidence["request_settings"]
        self.assertEqual(settings["top_level_effort"]["state"], "null_container")
        self.assertEqual(settings["thinking_type"]["state"], "unrecognized_container")
        self.assertEqual(settings["max_tokens"]["state"], "unrecognized")
        _, evidence = self.evidence(output_config={"effort": None})
        self.assertEqual(evidence["request_settings"]["top_level_effort"]["state"], "null")

    def test_unknown_strings_and_fields_are_not_copied(self):
        private = "arbitrary private setting" * 100
        _, evidence = self.evidence(
            thinking={"type": private, "budget_tokens": -1, "unknown": private},
            output_config={"effort": private, "unknown": private})
        settings = evidence["request_settings"]
        self.assertNotIn(private, json.dumps(settings))
        self.assertEqual(settings["thinking_type"]["state"], "unrecognized")
        self.assertEqual(settings["thinking_budget_tokens"]["state"], "unrecognized")

    def test_marker_storage_is_bounded_and_truncation_is_explicit(self):
        _, evidence = self.evidence(messages=[
            {"role": "system", "content": "private", "output_config": {"effort": "high"}}
            for _ in range(70)
        ])
        settings = evidence["request_settings"]
        self.assertEqual(len(settings["system_message_efforts"]), 64)
        self.assertEqual(settings["system_message_effort_count"], 70)
        self.assertTrue(settings["system_message_efforts_truncated"])
        self.assertLess(len(json.dumps(settings)), 10000)
        self.assertNotIn("private", json.dumps(settings))

    def test_optional_settings_leave_existing_context_audit_compatible(self):
        payload, evidence = self.evidence(thinking={"type": "enabled", "budget_tokens": 1024})
        charge = {**evidence, "attempt": 1, "request_bytes": evidence["outbound_body_bytes"]}
        self.assertEqual(evidence["system_messages_sha256"], context_digest(payload))
        self.assertEqual(audit_request_evidence([payload], [charge], required_version=1)["status"], "matched")
        del charge["request_settings"]
        self.assertEqual(audit_request_evidence([payload], [charge], required_version=1)["status"], "matched")


if __name__ == "__main__": unittest.main()
