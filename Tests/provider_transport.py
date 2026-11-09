#!/usr/bin/env python3
"""Loopback-only contracts for the real Lean ProviderIO/curl transport.

Python supplies independent test servers, not a production execution adapter.
The child receives only a synthetic credential, never the caller's API key.
"""
import http.server
import json
import os
from pathlib import Path
import subprocess
import tempfile
import threading
import time
import unittest


ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / ".lake/build/bin/runtime_contracts"
SENTINEL = "synthetic-test-key-never-send-to-loopback"


class Handler(http.server.BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *_args):
        pass

    def do_POST(self):
        body = self.rfile.read(int(self.headers.get("Content-Length", "0")))
        self.server.requests.append((self.path, dict(self.headers), body))
        self.server.received.set()
        if self.path == "/redirect":
            self.send_response(302)
            self.send_header("Location", f"http://127.0.0.1:{self.server.server_port}/followed")
            self.send_header("Content-Length", "0")
            self.end_headers()
            return
        if self.path == "/drip":
            self.send_response(200)
            self.send_header("Content-Length", "1000")
            self.end_headers()
            try:
                for _ in range(1000):
                    self.wfile.write(b"x")
                    self.wfile.flush()
                    time.sleep(0.05)
            except (BrokenPipeError, ConnectionResetError):
                pass
            return
        if self.path == "/chunked":
            self.send_response(200)
            self.send_header("Transfer-Encoding", "chunked")
            self.end_headers()
            try:
                for _ in range(128):
                    self.wfile.write(b"400\r\n" + b"x" * 1024 + b"\r\n")
                    self.wfile.flush()
                self.wfile.write(b"0\r\n\r\n")
            except (BrokenPipeError, ConnectionResetError):
                pass
            return
        response = b"\xff" if self.path == "/invalid-utf8" else body
        self.send_response(429 if self.path == "/rate" else 200)
        self.send_header("Content-Length", str(len(response) + (100 if self.path == "/partial" else 0)))
        self.send_header("Connection", "close")
        self.end_headers()
        self.wfile.write(response)
        self.wfile.flush()
        self.close_connection = True


class ProviderTransport(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="harness-http-contract-")
        self.home = Path(self.temporary.name)
        self.server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.server.daemon_threads = True
        self.server.requests = []
        self.server.received = threading.Event()
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        self.base = f"http://127.0.0.1:{self.server.server_port}"
        self.environment = {
            "PATH": os.defpath,
            "HOME": str(self.home),
            "LANG": "C.UTF-8",
            "ANTHROPIC_API_KEY": SENTINEL,
        }

    def tearDown(self):
        self.server.shutdown()
        self.server.server_close()
        self.thread.join(timeout=2)
        self.temporary.cleanup()

    def request(self, path="/echo", payload=None, **options):
        request = {"op": "http", "payload": {} if payload is None else payload,
                   "endpoint": self.base + path, "timeoutMs": 3000, **options}
        result = subprocess.run([str(BINARY)], input=json.dumps(request) + "\n", text=True,
                                capture_output=True, env=self.environment, timeout=8, check=True)
        self.assertNotIn(SENTINEL, result.stdout + result.stderr)
        return json.loads(result.stdout)

    def test_payload_escaping_and_no_loopback_credentials(self):
        payload = {"quotes": '"\\\n\r\t\x00', "unicode": "λ🙂", "injection": '\"\nurl = "https://invalid.example"'}
        result = self.request(payload=payload)
        self.assertEqual(result["status"], "ok")
        self.assertEqual(result["httpStatus"], 200)
        self.assertEqual(json.loads(result["body"]), payload)
        self.assertEqual(len(self.server.requests), 1)
        headers = {key.lower(): value for key, value in self.server.requests[0][1].items()}
        self.assertNotIn("x-api-key", headers)
        self.assertEqual(headers["content-type"], "application/json")

    def test_ambient_curl_config_and_proxy_are_ignored(self):
        trace = self.home / "forbidden-trace"
        (self.home / ".curlrc").write_text(f'location\nretry = 4\nheader = "x-ambient: unexpected"\ntrace = "{trace}"\n')
        self.environment.update({"CURL_HOME": str(self.home), "http_proxy": "http://127.0.0.1:1",
                                 "ALL_PROXY": "http://127.0.0.1:1", "SSLKEYLOGFILE": str(self.home / "keys")})
        result = self.request("/rate")
        self.assertEqual(result["httpStatus"], 429)
        self.assertEqual(len(self.server.requests), 1, "transport retried without core admission")
        headers = {key.lower(): value for key, value in self.server.requests[0][1].items()}
        self.assertNotIn("x-ambient", headers)
        self.assertFalse(trace.exists())
        self.assertFalse((self.home / "keys").exists())

    def test_redirect_is_returned_without_following(self):
        result = self.request("/redirect")
        self.assertEqual(result["httpStatus"], 302)
        self.assertEqual([item[0] for item in self.server.requests], ["/redirect"])

    def test_endpoint_confusion_rejected_before_dispatch(self):
        endpoints = ["https://invalid.example/messages", "http://127.0.0.1@invalid.example/",
                     "http://127.0.0.1.invalid.example/", "http://127.0.0.1:0/",
                     "http://127.0.0.1:65536/", "http://localhost/", "http://127.1/",
                     self.base + "/\nurl=other"]
        for endpoint in endpoints:
            with self.subTest(endpoint=endpoint):
                self.assertEqual(self.request(endpoint=endpoint)["status"], "failed")
        self.assertEqual(self.server.requests, [])

    def test_incomplete_and_invalid_utf8_bodies_are_uncertain(self):
        for path in ["/partial", "/invalid-utf8"]:
            with self.subTest(path=path):
                result = self.request(path)
                self.assertEqual(result["status"], "uncertain")
                self.assertNotIn("body", result)

    def test_chunked_body_obeys_response_limit(self):
        result = self.request("/chunked", responseBytes=4096)
        self.assertEqual(result["status"], "uncertain")
        self.assertNotIn("body", result)

    def test_total_deadline_stops_drip_response(self):
        started = time.monotonic()
        result = self.request("/drip", timeoutMs=250)
        self.assertIn(result["status"], {"interrupted", "uncertain"})
        self.assertLess(time.monotonic() - started, 2)
        self.assertEqual(len(self.server.requests), 1)

    def test_cancellation_stops_response_without_new_attempt(self):
        cancellation = self.home / "cancel"

        def cancel_after_dispatch():
            if self.server.received.wait(timeout=3):
                cancellation.write_text("cancel")

        canceller = threading.Thread(target=cancel_after_dispatch, daemon=True)
        canceller.start()
        result = self.request("/drip", cancelPath=str(cancellation))
        canceller.join(timeout=1)
        self.assertIn(result["status"], {"interrupted", "uncertain"})
        self.assertEqual(len(self.server.requests), 1)
        self.assertNotIn("body", result)


if __name__ == "__main__":
    unittest.main()
