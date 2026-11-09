"""Evaluation-only Anthropic relay. Credentials stay outside candidate processes.

Every forwarded request is counted, including SDK retries and summary requests.
The dollar ledger uses published token prices, with conservative byte-based
reservations for missing usage. It is not a provider-enforced billing cap.
"""
import http.server
import hashlib
import json
import os
from pathlib import Path
import threading
import time
from decimal import Decimal, ROUND_CEILING
from urllib.parse import urlparse
import urllib.error
import urllib.request
from campaign import CampaignLedger, NANOS
from lean_json import AuditError
from request_evidence import REQUEST_EVIDENCE_VERSION, outbound_evidence, user_text_digests

# Standard/global Opus 5.5 rates, checked against Anthropic's pricing page
# on 2026-11-09. Extended caching is reserved conservatively but not requested.
PRICES = {"input": 4.0, "output": 20.0, "cache_read": 0.2, "cache_write": 5.0, "cache_write_1h": 8.0}
RESPONSE_BYTES = 2_000_000
SETTLEMENT_TIMEOUT_SECONDS = 120


def output_ceiling(value):
    if type(value) is not int or not 1 <= value <= 8192:
        raise ValueError("max_output_tokens must be an integer from 1 through 8192")
    return value


def supported_pricing(payload):
    allowed = {"model", "max_tokens", "stream", "system", "messages", "tools", "tool_choice",
               "thinking", "output_config", "temperature", "top_p", "top_k", "stop_sequences",
               "metadata", "cache_control", "service_tier", "inference_geo", "speed"}
    if set(payload) - allowed:
        return False
    if payload.get("speed", "standard") != "standard" or payload.get("inference_geo", "global") != "global":
        return False
    if payload.get("service_tier", "auto") not in {"auto", "standard_only"}:
        return False

    def default_cache(value):
        if isinstance(value, dict):
            cache = value.get("cache_control")
            if cache is not None and (not isinstance(cache, dict) or cache.get("ttl", "5m") != "5m"):
                return False
            return all(default_cache(child) for child in value.values())
        return not isinstance(value, list) or all(default_cache(child) for child in value)

    tools = payload.get("tools", [])
    if not isinstance(tools, list) or any(not isinstance(tool, dict) or "type" in tool or "input_schema" not in tool for tool in tools):
        return False

    def content(value, permitted):
        if isinstance(value, str):
            return True
        if not isinstance(value, list):
            return False
        for block in value:
            if not isinstance(block, dict) or block.get("type") not in permitted:
                return False
            if block["type"] == "tool_result" and not content(block.get("content", ""), {"text"}):
                return False
        return True

    if not content(payload.get("system", ""), {"text"}):
        return False
    messages = payload.get("messages", [])
    if not isinstance(messages, list) or any(not isinstance(message, dict) or not content(
            message.get("content", ""), {"text", "tool_result", "tool_use", "thinking", "redacted_thinking"}) for message in messages):
        return False
    return default_cache(payload)


def unpriced_usage(usage):
    if not isinstance(usage, dict):
        return False
    server = usage.get("server_tool_use")
    return server is not None and (not isinstance(server, dict) or any(
        type(value) is not int or value != 0 for value in server.values()))


def usage_cost_nanos(usage, prices=PRICES):
    if not isinstance(usage, dict) or not all(k in usage for k in ("input_tokens", "output_tokens")):
        return None
    if unpriced_usage(usage):
        return None
    names = {"input_tokens": "input", "output_tokens": "output",
             "cache_read_input_tokens": "cache_read", "cache_creation_input_tokens": "cache_write"}
    if any(type(usage.get(name, 0)) is not int or usage.get(name, 0) < 0 for name in names):
        return None
    cache = usage.get("cache_creation")
    extra = Decimal(0)
    if cache is not None:
        if not isinstance(cache, dict):
            return None
        short, long = cache.get("ephemeral_5m_input_tokens", 0), cache.get("ephemeral_1h_input_tokens", 0)
        if any(type(value) is not int or value < 0 for value in [short, long]) or short + long != usage.get("cache_creation_input_tokens", 0):
            return None
        extra = Decimal(long) * (Decimal(str(prices["cache_write_1h"])) - Decimal(str(prices["cache_write"]))) * 1000
    amount = sum(Decimal(usage.get(name, 0)) * Decimal(str(prices[price])) * 1000
                 for name, price in names.items()) + extra
    return int(amount.to_integral_value(rounding=ROUND_CEILING))


def usage_cost(usage, prices=PRICES):
    nanos = usage_cost_nanos(usage, prices)
    return None if nanos is None else nanos / NANOS


def response_usage(body, streaming):
    if not streaming:
        try:
            return json.loads(body).get("usage")
        except (ValueError, AttributeError):
            return None
    usage, complete, final_usage, started = {}, False, False, False
    for line in body.splitlines():
        if not line.startswith(b"data: "):
            continue
        try:
            event = json.loads(line[6:])
        except ValueError:
            return None
        if not isinstance(event, dict):
            return None
        if event.get("type") == "ping":
            continue
        if complete:
            return None
        if event.get("type") == "message_start":
            if started or not isinstance(event.get("message"), dict):
                return None
            initial = event["message"].get("usage", {})
            if not isinstance(initial, dict):
                return None
            if unpriced_usage(initial):
                return initial  # Preserve evidence even if a later event replaces it.
            if usage_cost_nanos(initial) is None:
                return None
            usage.update(initial)
            started = True
        elif event.get("type") == "message_delta":
            if not started:
                return None
            final = event.get("usage", {})
            final_usage = isinstance(final, dict) and type(final.get("output_tokens")) is int and final["output_tokens"] >= 0
            if not final_usage:
                return None
            if unpriced_usage(final):
                return final
            for key in ["input_tokens", "output_tokens", "cache_read_input_tokens", "cache_creation_input_tokens"]:
                if key in final and (type(final[key]) is not int or final[key] < 0 or
                                     (type(usage.get(key)) is int and final[key] < usage[key])):
                    return None
            if "cache_creation" in final:
                nested = final["cache_creation"]
                previous = usage.get("cache_creation", {})
                if not isinstance(nested, dict) or not isinstance(previous, dict):
                    return None
                for key in ["ephemeral_5m_input_tokens", "ephemeral_1h_input_tokens"]:
                    count = nested.get(key, 0)
                    if type(count) is not int or count < previous.get(key, 0):
                        return None
            usage.update(final)
            if usage_cost_nanos(usage) is None:
                return None
        elif event.get("type") == "message_stop":
            if not started or not final_usage:
                return None
            complete = True
        elif event.get("type") == "error":
            return None
    return usage if complete and final_usage else None


class Broker:
    def __init__(self, key, output, budget=50.0, model="claude-opus-5-5", upstream=None,
                 campaign=None, allocation=None, retain_responses=False):
        if model != "claude-opus-5-5":
            raise ValueError("evaluation pricing is pinned to claude-opus-5-5; configure and review rates before changing model")
        self.key, self.output, self.budget, self.model = key, Path(output), budget, model
        self.upstream = upstream or "https://api.anthropic.com/v1/messages"
        endpoint = urlparse(self.upstream)
        offline = endpoint.scheme == "http" and endpoint.hostname in {"127.0.0.1", "::1"}
        if not offline and (campaign is None or allocation is None):
            raise ValueError("live evaluation requires a shared campaign ledger and allocation")
        self.campaign = CampaignLedger(campaign) if campaign is not None else None
        self.allocation = allocation
        self.output.mkdir(parents=True, exist_ok=True, mode=0o700)
        if type(retain_responses) is not bool:
            raise ValueError("retain_responses must be an explicit Boolean")
        self.retain_responses = retain_responses
        if retain_responses:
            (self.output / "response-evidence").mkdir(mode=0o700, exist_ok=False)
        self.lock, self.runs, self.records = threading.Lock(), {}, []
        self.settled = threading.Condition(self.lock)
        self.total = 0.0
        self.storage_failure = None
        self.request_evidence_failure = None
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
                body = bytearray()
                received_bytes, http_status = 0, None
                transport_complete, transport_error = False, None
                forwarding_invoked = False
                try:
                    length = int(self.headers.get("Content-Length", "0"))
                    if not 0 < length <= 400_000:
                        return self.reject(413, "request byte ceiling exceeded")
                    raw = self.rfile.read(length)
                    # Construct the actual Request first; its immutable data bytes
                    # are exactly those hashed and later passed to opener.open.
                    # Authentication headers remain transient and are never logged.
                    headers = {"Content-Type": "application/json", "anthropic-version": "2023-06-01", "x-api-key": broker.key}
                    beta = self.headers.get("anthropic-beta")
                    if beta:
                        headers["anthropic-beta"] = beta
                    request = urllib.request.Request(broker.upstream, data=raw, headers=headers)
                    try:
                        if len(raw) != length:
                            raise ValueError("incomplete request body")
                        payload, request_evidence = outbound_evidence(request.data)
                    except (AuditError, ValueError, UnicodeError, ArithmeticError, RecursionError) as error:
                        with broker.settled:
                            run = broker.runs.get(run_id)
                            if run is None or run["closed"]:
                                return self.reject(403, "evaluation run is closed")
                            broker.request_evidence_failure = {"kind": "request_evidence",
                                "error": type(error).__name__, "at_unix": time.time()}
                            run["admission_refusal"] = dict(broker.request_evidence_failure)
                            try:
                                broker.save()
                            finally:
                                broker.settled.notify_all()
                        return self.reject(400, "outbound request evidence admission failed; no request forwarded")
                    tokens = payload.get("max_tokens", 0)
                    if payload.get("model") != broker.model or type(tokens) is not int or not 0 < tokens <= 8192:
                        return self.reject(400, "model/output ceiling mismatch")
                    if not supported_pricing(payload):
                        return self.reject(400, "request pricing tier or cache duration differs from the evaluation plan")
                    reservation_nanos = int(((len(raw) + 32768) * Decimal(str(max(PRICES["input"], PRICES["cache_write_1h"]))) * 1000 +
                                             tokens * Decimal(str(PRICES["output"])) * 1000).to_integral_value(rounding=ROUND_CEILING))
                    reservation = reservation_nanos / NANOS
                    with broker.settled:
                        # Clients can receive the last response byte before this
                        # handler has durably settled usage. Serialize admission
                        # through that boundary, including across run IDs.
                        deadline = time.monotonic() + SETTLEMENT_TIMEOUT_SECONDS
                        while True:
                            run = broker.runs.get(run_id)
                            if run is None or run["closed"]:
                                return self.reject(403, "evaluation run is closed")
                            if tokens > run["max_output_tokens"]:
                                return self.reject(400, "evaluation run output ceiling exceeded")
                            if broker.storage_failure is not None:
                                run["admission_refusal"] = {"kind": "broker_storage", "at_unix": time.time()}
                                broker.save()
                                return self.reject(400, "broker evidence storage failed; no new request admitted")
                            if broker.request_evidence_failure is not None:
                                run["admission_refusal"] = dict(broker.request_evidence_failure)
                                broker.save()
                                return self.reject(400, "earlier request evidence failed; no new request admitted")
                            if not any(prior.get("active") for prior in broker.records):
                                break
                            remaining = deadline - time.monotonic()
                            if remaining <= 0:
                                run["admission_refusal"] = {"kind": "unsettled_accounting", "at_unix": time.time(),
                                                            "reason": "earlier request remains active after settlement deadline"}
                                broker.save()
                                return self.reject(400, "earlier provider accounting is still active; no new request admitted")
                            broker.settled.wait(timeout=remaining)
                        if any(not prior.get("accounting_settled") for prior in broker.records):
                            run["admission_refusal"] = {"kind": "unsettled_accounting", "at_unix": time.time()}
                            broker.save()
                            return self.reject(400, "earlier provider accounting is unsettled; inspect before further paid work")
                        if run["attempts"] >= run["max_attempts"] or length > run["max_request_bytes"]:
                            return self.reject(400, "evaluation call/context ceiling exhausted")
                        if broker.total + reservation > broker.budget:
                            run["admission_refusal"] = {"kind": "local_budget", "reserved_usd": reservation,
                                                        "at_unix": time.time()}
                            broker.save()
                            return self.reject(400, "evaluation spending allowance exhausted")
                        campaign_request = None
                        if broker.campaign is not None:
                            try:
                                campaign_request = broker.campaign.reserve(broker.allocation, run_id, reservation_nanos)
                            except (ValueError, OSError):
                                run["admission_refusal"] = {"kind": "shared_campaign", "reserved_usd": reservation,
                                                            "at_unix": time.time()}
                                broker.save()
                                return self.reject(400, "shared campaign admission failed; inspect accounting before further paid work")
                        run["attempts"] += 1
                        broker.total += reservation
                        record = {"run_id": run_id, "attempt": run["attempts"], "request_bytes": length,
                                  "max_tokens": tokens, "max_output_tokens": run["max_output_tokens"],
                                  "stream": bool(payload.get("stream")),
                                  "reserved_usd": reservation, "charged_usd": reservation, "usage": None,
                                  "status": "unknown", "started": time.time(), "active": True,
                                  "accounting_settled": False,
                                  **request_evidence, "outbound_transport_state": "dispatch_intent"}
                        if run["attempts"] == 1:
                            record["initial_user_text_sha256"] = user_text_digests(payload)
                        if broker.retain_responses:
                            record["response_evidence_index"] = len(broker.records)
                        if campaign_request is not None:
                            record["campaign_request_id"] = campaign_request
                        broker.records.append(record)
                        broker.save()
                    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}), NoRedirect())
                    started = time.monotonic()
                    try:
                        forwarding_invoked = True
                        response = opener.open(request, timeout=90)
                    except urllib.error.HTTPError as error:
                        response = error
                    with response:
                        http_status = response.status
                        expected_length = response.length
                        self.send_response(response.status)
                        self.send_header("Content-Type", response.headers.get("Content-Type", "application/json"))
                        if expected_length is not None:
                            self.send_header("Content-Length", str(expected_length))
                        self.end_headers()
                        disconnected = False
                        while True:
                            chunk = response.read1(65536)
                            if not chunk:
                                break
                            received_bytes += len(chunk)
                            body.extend(chunk[:max(0, RESPONSE_BYTES - len(body))])
                            if received_bytes > RESPONSE_BYTES or time.monotonic() - started > 100:
                                raise RuntimeError("response allowance exhausted")
                            if not disconnected:
                                try:
                                    self.wfile.write(chunk)
                                    self.wfile.flush()
                                except (BrokenPipeError, ConnectionResetError):
                                    disconnected = True
                        if expected_length is not None and received_bytes != expected_length:
                            raise RuntimeError("provider response ended before its declared length")
                        transport_complete = True
                        usage = response_usage(bytes(body), bool(payload.get("stream")))
                        cost = usage_cost(usage)
                        with broker.lock:
                            if unpriced_usage(usage) and broker.campaign is not None:
                                broker.campaign.freeze("provider reported unpriced server-tool usage")
                            if cost is not None and broker.campaign is not None:
                                broker.campaign.settle(campaign_request, usage_cost_nanos(usage), usage)
                            record.update(status=response.status, usage=usage, elapsed_seconds=time.monotonic()-started)
                            if cost is not None:
                                broker.total += cost - reservation
                                record["charged_usd"] = cost
                                record["accounting_settled"] = True
                            broker.save()
                except Exception as error:
                    # Lost outcomes retain their reservation. No hidden retry.
                    transport_error = None if transport_complete else type(error).__name__
                    self.close_connection = True
                finally:
                    if record is not None:
                        evidence = None
                        if broker.retain_responses:
                            # Diagnostic storage is independent of cost settlement.
                            # These bytes are never replayed into the candidate.
                            evidence = broker.retain_response(
                                record["response_evidence_index"], bytes(body), received_bytes,
                                http_status, transport_complete, transport_error)
                        with broker.settled:
                            if evidence is not None:
                                record["response_evidence"] = evidence
                            record['active'] = False
                            record['outbound_transport_state'] = (
                                'response_observed' if http_status is not None else
                                'attempted' if forwarding_invoked else 'not_started')
                            record['outbound_http_status'] = http_status
                            record['outbound_transport_complete'] = transport_complete
                            try:
                                broker.save()
                            except Exception:
                                # save retains a sticky failure; a later write
                                # cannot silently erase the failed boundary.
                                pass
                            finally:
                                broker.settled.notify_all()

        self.server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)

    def retain_response(self, index, body, received_bytes, http_status, complete, error):
        metadata = {"sha256": hashlib.sha256(body).hexdigest(), "captured_bytes": len(body),
                    "received_bytes": received_bytes, "http_status": http_status,
                    "transport_complete": complete, "transport_error": error,
                    "prefix_truncated": received_bytes > len(body),
                    "scope": "Exact bounded provider-body bytes; completeness describes transport, not core acceptance."}
        path = self.output / "response-evidence" / f"response-{index:06d}.body"
        try:
            fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
            try:
                remaining = memoryview(body)
                while remaining:
                    count = os.write(fd, remaining)
                    if count <= 0:
                        raise OSError("diagnostic body write made no progress")
                    remaining = remaining[count:]
                os.fsync(fd)
            finally:
                os.close(fd)
            directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(directory)
            finally:
                os.close(directory)
            metadata.update(status="stored", path=str(path.relative_to(self.output)))
        except Exception as storage_error:
            metadata.update(status="storage_failed", storage_error=type(storage_error).__name__)
        return metadata

    def add_run(self, run_id, max_attempts=12, max_request_bytes=160000, max_output_tokens=4096):
        max_output_tokens = output_ceiling(max_output_tokens)
        with self.lock:
            if run_id in self.runs:
                raise ValueError("duplicate evaluation run")
            self.runs[run_id] = {"attempts": 0, "max_attempts": max_attempts,
                                 "max_request_bytes": max_request_bytes,
                                 "max_output_tokens": max_output_tokens, "closed": False}
        return f"http://127.0.0.1:{self.server.server_port}/{run_id}/v1/messages"

    def close_run(self, run_id):
        with self.settled:
            self.runs[run_id]["closed"] = True
            deadline = time.monotonic() + SETTLEMENT_TIMEOUT_SECONDS
            while any(r.get('active') for r in self.records if r['run_id'] == run_id):
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    raise TimeoutError('provider accounting did not settle')
                self.settled.wait(timeout=remaining)
            self.save()
            if self.storage_failure is not None:
                raise RuntimeError('broker evidence storage failed; durable campaign charges are retained')
            if self.request_evidence_failure is not None:
                raise RuntimeError('outbound request evidence admission failed; no further request admitted')
            if any(not r.get("accounting_settled") for r in self.records if r['run_id'] == run_id):
                raise RuntimeError('provider accounting did not settle; reservation retained')

    def admission_refusal(self, run_id):
        with self.lock:
            value = self.runs.get(run_id, {}).get("admission_refusal")
            return dict(value) if value is not None else None

    def save(self):
        try:
            self._save()
        except Exception as error:
            if self.storage_failure is None:
                self.storage_failure = {"error": type(error).__name__, "detail": str(error), "at_unix": time.time()}
            raise

    def _save(self):
        path = self.output / "broker.json"
        temporary = path.with_suffix(".tmp")
        with temporary.open("w") as file:
            json.dump({"model": self.model, "prices_per_million": PRICES,
                       "budget_usd": self.budget, "accounted_usd": self.total, "records": self.records,
                       "retain_responses": self.retain_responses,
                       "request_evidence_version": REQUEST_EVIDENCE_VERSION,
                       "request_evidence_failure": self.request_evidence_failure,
                       "storage_failure": self.storage_failure,
                       "admission_refusals": {ident: run["admission_refusal"] for ident, run in self.runs.items()
                                              if run.get("admission_refusal") is not None},
                       "campaign_dir": str(self.campaign.directory) if self.campaign is not None else None,
                       "allocation": self.allocation}, file, indent=2, allow_nan=False)
            file.write("\n"); file.flush(); os.fsync(file.fileno())
        os.replace(temporary, path)
        directory = os.open(path.parent, os.O_DIRECTORY | os.O_RDONLY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)

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
