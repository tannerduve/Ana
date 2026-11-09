"""Evaluation-only Anthropic relay. Credentials stay outside candidate processes.

Every forwarded request is counted, including SDK retries and summary requests.
The dollar ledger uses published token prices, with conservative byte-based
reservations for missing usage. It is not a provider-enforced billing cap.
"""
import http.server
import json
import os
from pathlib import Path
import threading
import time
import urllib.error
import urllib.request

PRICES = {"input": 4.0, "output": 20.0, "cache_read": 0.2, "cache_write": 5.0}


def usage_cost(usage, prices=PRICES):
    if not isinstance(usage, dict) or not all(k in usage for k in ("input_tokens", "output_tokens")):
        return None
    return (usage["input_tokens"] * prices["input"] + usage["output_tokens"] * prices["output"] +
            usage.get("cache_read_input_tokens", 0) * prices["cache_read"] +
            usage.get("cache_creation_input_tokens", 0) * prices["cache_write"]) / 1_000_000


def response_usage(body, streaming):
    if not streaming:
        try:
            return json.loads(body).get("usage")
        except (ValueError, AttributeError):
            return None
    usage, complete = {}, False
    for line in body.splitlines():
        if not line.startswith(b"data: "):
            continue
        try:
            event = json.loads(line[6:])
        except ValueError:
            continue
        if event.get("type") == "message_start":
            usage.update(event.get("message", {}).get("usage", {}))
        elif event.get("type") == "message_delta":
            usage.update(event.get("usage", {}))
        elif event.get("type") == "message_stop":
            complete = True
    return usage if complete else None


class Broker:
    def __init__(self, key, output, budget=50.0, model="claude-opus-5-5", upstream=None):
        self.key, self.output, self.budget, self.model = key, Path(output), budget, model
        self.upstream = upstream or "https://api.anthropic.com/v1/messages"
        self.output.mkdir(parents=True, exist_ok=True, mode=0o700)
        self.lock, self.runs, self.records = threading.Lock(), {}, []
        self.settled = threading.Condition(self.lock)
        self.total = 0.0
        broker = self

        class Handler(http.server.BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.0"

            def log_message(self, *_):
                pass

            def reject(self, status, message):
                body = json.dumps({"type": "error", "error": {"type": "invalid_request_error", "message": message}}).encode()
                self.send_response(status)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            def do_POST(self):
                # A per-run capability prevents accidentally charging another run.
                # It does not protect against a malicious candidate that sees its URL.
                parts = self.path.split("?")[0].strip("/").split("/")
                if len(parts) != 3 or parts[1:] != ["v1", "messages"]:
                    return self.reject(404, "unknown evaluation endpoint")
                run_id = parts[0]
                record = None
                try:
                    length = int(self.headers.get("Content-Length", "0"))
                    if not 0 < length <= 400_000:
                        return self.reject(413, "request byte ceiling exceeded")
                    raw = self.rfile.read(length)
                    payload = json.loads(raw)
                    tokens = payload.get("max_tokens", 0)
                    if payload.get("model") != broker.model or not isinstance(tokens, int) or not 0 < tokens <= 4096:
                        return self.reject(400, "model/output ceiling mismatch")
                    reservation = ((len(raw) + 32768) * max(PRICES["input"], PRICES["cache_write"]) + tokens * PRICES["output"]) / 1_000_000
                    with broker.lock:
                        run = broker.runs.get(run_id)
                        if run is None or run["closed"]:
                            return self.reject(403, "evaluation run is closed")
                        if run["attempts"] >= run["max_attempts"] or length > run["max_request_bytes"]:
                            return self.reject(400, "evaluation call/context ceiling exhausted")
                        if broker.total + reservation > broker.budget:
                            return self.reject(400, "evaluation spending allowance exhausted")
                        run["attempts"] += 1
                        broker.total += reservation
                        record = {"run_id": run_id, "attempt": run["attempts"], "request_bytes": length,
                                  "max_tokens": tokens, "stream": bool(payload.get("stream")),
                                  "reserved_usd": reservation, "charged_usd": reservation, "usage": None,
                                  "status": "unknown", "started": time.time(), "active": True}
                        broker.records.append(record)
                        broker.save()
                    # Never persist authentication headers or the credential.
                    headers = {"Content-Type": "application/json", "anthropic-version": "2023-06-01", "x-api-key": broker.key}
                    beta = self.headers.get("anthropic-beta")
                    if beta:
                        headers["anthropic-beta"] = beta
                    request = urllib.request.Request(broker.upstream, data=raw, headers=headers)
                    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}), NoRedirect())
                    started = time.monotonic()
                    body = bytearray()
                    try:
                        response = opener.open(request, timeout=90)
                    except urllib.error.HTTPError as error:
                        response = error
                    with response:
                        self.send_response(response.status)
                        self.send_header("Content-Type", response.headers.get("Content-Type", "application/json"))
                        self.end_headers()
                        disconnected = False
                        while True:
                            chunk = response.read1(65536)
                            if not chunk:
                                break
                            body.extend(chunk)
                            if len(body) > 2_000_000 or time.monotonic() - started > 100:
                                raise RuntimeError("response allowance exhausted")
                            if not disconnected:
                                try:
                                    self.wfile.write(chunk)
                                    self.wfile.flush()
                                except (BrokenPipeError, ConnectionResetError):
                                    disconnected = True
                        usage = response_usage(bytes(body), bool(payload.get("stream")))
                        cost = usage_cost(usage)
                        with broker.lock:
                            record.update(status=response.status, usage=usage, elapsed_seconds=time.monotonic()-started)
                            if cost is not None:
                                broker.total += cost - reservation
                                record["charged_usd"] = cost
                            broker.save()
                except Exception:
                    # Lost outcomes retain their reservation. No hidden retry.
                    self.close_connection = True
                finally:
                    if record is not None:
                        with broker.settled:
                            record['active'] = False
                            broker.save()
                            broker.settled.notify_all()

        self.server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)

    def add_run(self, run_id, max_attempts=12, max_request_bytes=160000):
        with self.lock:
            if run_id in self.runs:
                raise ValueError("duplicate evaluation run")
            self.runs[run_id] = {"attempts": 0, "max_attempts": max_attempts,
                                 "max_request_bytes": max_request_bytes, "closed": False}
        return f"http://127.0.0.1:{self.server.server_port}/{run_id}/v1/messages"

    def close_run(self, run_id):
        with self.settled:
            self.runs[run_id]["closed"] = True
            deadline = time.monotonic() + 120
            while any(r.get('active') for r in self.records if r['run_id'] == run_id):
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    raise TimeoutError('provider accounting did not settle')
                self.settled.wait(timeout=remaining)
            self.save()

    def save(self):
        path = self.output / "broker.json"
        temporary = path.with_suffix(".tmp")
        temporary.write_text(json.dumps({"model": self.model, "prices_per_million": PRICES,
            "budget_usd": self.budget, "accounted_usd": self.total, "records": self.records}, indent=2)+"\n")
        os.replace(temporary, path)

    def __enter__(self):
        self.thread.start()
        return self

    def __exit__(self, *_):
        self.server.shutdown()
        self.server.server_close()
        self.thread.join()


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *_):
        return None
