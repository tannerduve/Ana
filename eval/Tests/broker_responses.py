"""Unpaid wire-body retention, transport truncation and independent accounting."""
import hashlib
import http.client
import http.server
import json
from pathlib import Path
import stat
import sys
import tempfile
import threading
import unittest
from unittest.mock import patch
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "runner"))
import broker as module


class ResponseEvidence(unittest.TestCase):
    def request(self, directory, body, *, streaming=False, length_extra=0, storage_failure=False, retain=True,
                campaign=None):
        class Provider(http.server.BaseHTTPRequestHandler):
            def log_message(self, *_): pass
            def do_POST(self):
                self.rfile.read(int(self.headers["Content-Length"]))
                self.send_response(200)
                self.send_header("Content-Type", "text/event-stream" if streaming else "application/json")
                self.send_header("Content-Length", str(len(body) + length_extra))
                self.end_headers()
                self.wfile.write(body)
        server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Provider)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            with module.Broker("synthetic-key-not-in-evidence", directory, upstream=f"http://127.0.0.1:{server.server_port}",
                               retain_responses=retain, campaign=campaign,
                               allocation="fixture" if campaign else None) as relay:
                endpoint = relay.add_run("fixture")
                original = module.os.open
                def open_file(path, *args, **kwargs):
                    if storage_failure and str(path).endswith(".body"):
                        raise OSError("injected diagnostic disk failure")
                    return original(path, *args, **kwargs)
                request = urllib.request.Request(endpoint, json.dumps({"model": relay.model,
                    "max_tokens": 4096, "stream": streaming, "messages": []}).encode())
                incomplete = False
                with patch.object(module.os, "open", side_effect=open_file):
                    try:
                        with urllib.request.urlopen(request, timeout=10) as response:
                            forwarded = response.read()
                    except http.client.IncompleteRead as error:
                        forwarded, incomplete = error.partial, True
                    try:
                        relay.close_run("fixture")
                        settled = True
                    except RuntimeError:
                        settled = False
                return relay.records[0], forwarded, settled, incomplete
        finally:
            server.shutdown(); server.server_close(); thread.join()

    def test_complete_json_and_sse_are_exact_private_diagnostic_bytes(self):
        complete = json.dumps({"usage": {"input_tokens": 3, "output_tokens": 2}}).encode()
        events = [{"type": "message_start", "message": {"usage": {"input_tokens": 3, "output_tokens": 0}}},
                  {"type": "message_delta", "usage": {"output_tokens": 2}}, {"type": "message_stop"}]
        streaming = b"".join(b"data: " + json.dumps(event).encode() + b"\n\n" for event in events)
        for body, stream in [(complete, False), (streaming, True)]:
            with self.subTest(stream=stream), tempfile.TemporaryDirectory() as temporary:
                directory = Path(temporary)
                record, forwarded, settled, incomplete = self.request(directory, body, streaming=stream)
                evidence = record["response_evidence"]
                self.assertTrue(settled)
                self.assertFalse(incomplete)
                self.assertEqual(forwarded, body)
                self.assertTrue(evidence["transport_complete"])
                self.assertFalse(evidence["prefix_truncated"])
                saved = directory / evidence["path"]
                self.assertEqual(saved.read_bytes(), body)
                self.assertEqual(evidence["sha256"], hashlib.sha256(body).hexdigest())
                self.assertEqual(evidence["captured_bytes"], len(body))
                self.assertEqual(stat.S_IMODE(saved.stat().st_mode), 0o600)
                self.assertNotIn("synthetic-key-not-in-evidence", (directory / "broker.json").read_text())

    def test_transport_truncation_is_not_made_complete_or_zero_cost(self):
        body = b'{"usage":{"input_tokens":3,"output_tokens":2}}'
        with tempfile.TemporaryDirectory() as temporary:
            record, forwarded, settled, incomplete = self.request(Path(temporary), body, length_extra=50)
            self.assertFalse(settled)
            self.assertTrue(incomplete)
            self.assertEqual(forwarded, body)
            self.assertFalse(record["response_evidence"]["transport_complete"])
            self.assertEqual(record["charged_usd"], record["reserved_usd"])
            self.assertIsNone(record["usage"])

    def test_oversized_body_retains_bounded_prefix_without_fabricated_terminal(self):
        body = b"x" * (module.RESPONSE_BYTES + 100)
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            record, forwarded, settled, incomplete = self.request(directory, body, streaming=True)
            evidence = record["response_evidence"]
            self.assertFalse(settled)
            self.assertTrue(incomplete)
            self.assertTrue(evidence["prefix_truncated"])
            self.assertFalse(evidence["transport_complete"])
            self.assertEqual((directory / evidence["path"]).read_bytes(), body[:module.RESPONSE_BYTES])
            self.assertLess(len(forwarded), len(body))
            self.assertNotIn(b"message_stop", forwarded)

    def test_diagnostic_write_failure_cannot_erase_known_usage_settlement(self):
        body = b'{"usage":{"input_tokens":3,"output_tokens":2}}'
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            evidence = directory / "prior.json"
            evidence.write_text('{"authorized_budget_usd":10,"total_accounted_usd":0}')
            campaign = directory / "campaign"
            module.CampaignLedger.initialize(campaign, evidence, {"fixture": 10})
            record, forwarded, settled, incomplete = self.request(directory, body, storage_failure=True, campaign=campaign)
            self.assertTrue(settled)
            self.assertFalse(incomplete)
            self.assertEqual(forwarded, body)
            self.assertEqual(record["charged_usd"], module.usage_cost({"input_tokens": 3, "output_tokens": 2}))
            self.assertEqual(record["response_evidence"]["status"], "storage_failed")
            self.assertTrue(record["accounting_settled"])
            saved = module.CampaignLedger(campaign).snapshot()
            self.assertEqual(saved["accounted_nanos"], module.usage_cost_nanos({"input_tokens": 3, "output_tokens": 2}))
            self.assertTrue(all(row["settled"] for row in saved["requests"].values()))

    def test_retention_is_off_unless_explicitly_requested(self):
        body = b'{"usage":{"input_tokens":3,"output_tokens":2}}'
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            record, _, settled, _ = self.request(directory, body, retain=False)
            self.assertTrue(settled)
            self.assertNotIn("response_evidence", record)
            self.assertFalse((directory / "response-evidence").exists())


if __name__ == "__main__": unittest.main()
