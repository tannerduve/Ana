"""Shared accounting survives restart, concurrency, malformed usage and storage faults."""
from concurrent.futures import ThreadPoolExecutor
from contextlib import nullcontext
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
from campaign import CampaignLedger, money
from broker import Broker, usage_cost_nanos, response_usage, supported_pricing, unpriced_usage
import broker as broker_module


class Campaign(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.evidence = self.root / "prior.json"
        self.evidence.write_text(json.dumps({"authorized_budget_usd": "10", "total_accounted_usd": "2"}))
        self.path = self.root / "campaign"
        self.ledger = CampaignLedger.initialize(self.path, self.evidence, {"development": "4", "reserved": "4"})

    def test_restart_keeps_unknown_reservations_and_exact_settlement(self):
        ident = self.ledger.reserve("development", "run", money("3"))
        restarted = CampaignLedger(self.path)
        self.assertEqual(restarted.snapshot()["accounted_nanos"], money("5"))
        with self.assertRaisesRegex(ValueError, "exhausted"):
            restarted.reserve("development", "other", money("2"))
        restarted.settle(ident, money("0.4"), {"input_tokens": 100000})
        before = (self.path / "ledger.jsonl").read_bytes()
        restarted.settle(ident, money("0.4"), {"input_tokens": 100000})
        self.assertEqual((self.path / "ledger.jsonl").read_bytes(), before)
        self.assertEqual(restarted.snapshot()["accounted_nanos"], money("2.4"))
        with self.assertRaisesRegex(ValueError, "differently"):
            restarted.settle(ident, money("0.3"), {})

    def test_concurrent_brokers_share_one_ceiling(self):
        def reserve(number):
            try:
                return CampaignLedger(self.path).reserve("development", str(number), money("1"))
            except ValueError:
                return None
        with ThreadPoolExecutor(max_workers=12) as executor:
            accepted = list(executor.map(reserve, range(20)))
        self.assertEqual(sum(value is not None for value in accepted), 4)
        self.assertEqual(len(set(value for value in accepted if value is not None)), 4)
        self.assertEqual(self.ledger.snapshot()["accounted_nanos"], money("6"))

    def test_transfer_survives_restart_without_changing_authorization_or_cost(self):
        ident = self.ledger.reserve("development", "finished", money("3"))
        self.ledger.settle(ident, money("1"), {})
        before = self.ledger.snapshot()
        self.ledger.transfer("development", "reserved", money("3"), "Freeze next cohort")
        reopened = CampaignLedger(self.path)
        after = reopened.snapshot()
        self.assertEqual(after["allocations_nanos"], {"development": money("1"), "reserved": money("7")})
        for field in ["authorized_nanos", "prior_accounted_nanos", "accounted_nanos", "requests"]:
            self.assertEqual(after[field], before[field])
        self.assertEqual(sum(after["allocations_nanos"].values()), sum(before["allocations_nanos"].values()))
        with self.assertRaisesRegex(ValueError, "exhausted"):
            reopened.reserve("development", "too-much", 1)
        reopened.reserve("reserved", "admitted", money("7"))
        self.assertEqual(reopened.snapshot()["accounted_nanos"], money("10"))

    def test_invalid_transfers_leave_ledger_unchanged(self):
        original = (self.path / "ledger.jsonl").read_bytes()
        for source, destination, amount, reason in [
                ("development", "reserved", money("5"), "excess"),
                ("missing", "reserved", 1, "unknown"),
                ("development", "development", 1, "same"),
                ([], "reserved", 1, "bad name"),
                ("development", "reserved", True, "bad amount"),
                ("development", "reserved", 0, "zero"),
                ("development", "reserved", -1, "negative"),
                ("development", "reserved", 1, " ")]:
            with self.subTest(source=source, amount=amount):
                with self.assertRaises(ValueError):
                    self.ledger.transfer(source, destination, amount, reason)
                self.assertEqual((self.path / "ledger.jsonl").read_bytes(), original)

    def test_pending_or_frozen_campaign_cannot_transfer(self):
        ident = self.ledger.reserve("reserved", "uncertain", money("1"))
        for freeze in [False, True]:
            if freeze:
                self.ledger.settle(ident, money("0.1"), {})
                self.ledger.freeze("review required")
            before = (self.path / "ledger.jsonl").read_bytes()
            with self.assertRaisesRegex(ValueError, "unfrozen, settled"):
                self.ledger.transfer("development", "reserved", money("1"), "blocked")
            self.assertEqual((self.path / "ledger.jsonl").read_bytes(), before)

    def test_replay_rejects_checksummed_invalid_transfer(self):
        with self.ledger._locked() as (fd, state):
            self.ledger._write(fd, state["next_sequence"], {
                "kind": "transfer", "from": "development", "to": "reserved",
                "amount_nanos": money("5"), "reason": "invalid fixture"})
        with self.assertRaisesRegex(ValueError, "unspent"):
            CampaignLedger(self.path)

    def test_over_reservation_charge_freezes_further_admission(self):
        ident = self.ledger.reserve("development", "run", money("0.1"))
        self.ledger.settle(ident, money("0.2"), {"input_tokens": 1})
        self.assertTrue(self.ledger.snapshot()["frozen"])
        with self.assertRaisesRegex(ValueError, "frozen"):
            self.ledger.reserve("reserved", "other", money("0.1"))

    def test_corrupt_or_torn_accounting_refuses_resume(self):
        original = (self.path / "ledger.jsonl").read_bytes()
        for invalid in [original + b'{"seq":1', original.replace(b'"version":1', b'"version":2')]:
            with self.subTest(invalid=invalid[-20:]):
                (self.path / "ledger.jsonl").write_bytes(invalid)
                with self.assertRaises(ValueError):
                    CampaignLedger(self.path)
        (self.path / "ledger.jsonl").write_bytes(original)

    def test_failed_flush_cannot_release_reserved_funds(self):
        with patch("campaign.os.fsync", side_effect=OSError("injected flush failure")):
            with self.assertRaises(OSError):
                self.ledger.reserve("development", "unlaunched", money("3"))
        # Complete but unacknowledged data remains conservatively charged here.
        self.assertEqual(CampaignLedger(self.path).snapshot()["accounted_nanos"], money("5"))

    def test_usage_and_initial_allocation_validation(self):
        for usage in [{}, {"input_tokens": -1, "output_tokens": 10},
                      {"input_tokens": True, "output_tokens": 10},
                      {"input_tokens": 10, "output_tokens": "20"},
                      {"input_tokens": 10, "output_tokens": 20, "cache_read_input_tokens": -1}]:
            self.assertIsNone(usage_cost_nanos(usage))
        self.assertEqual(usage_cost_nanos({"input_tokens": 10, "output_tokens": 20}), 440000)
        self.assertEqual(usage_cost_nanos({"input_tokens": 0, "output_tokens": 0,
            "cache_creation_input_tokens": 100, "cache_creation": {
                "ephemeral_5m_input_tokens": 60, "ephemeral_1h_input_tokens": 40}}), 620000)
        for payload in [{"speed": "fast"}, {"inference_geo": "us"},
                        {"messages": [{"cache_control": {"type": "ephemeral", "ttl": "1h"}}]},
                        {"tools": [{"type": "web_search_20250305", "name": "web_search"}]},
                        {"mcp_servers": []}, {"container": {}},
                        {"messages": [{"content": [{"type": "document", "source": {"type": "url", "url": "https://example.invalid"}}]}]}]:
            self.assertFalse(supported_pricing(payload))
        self.assertTrue(supported_pricing({"cache_control": {"type": "ephemeral"}}))
        with self.assertRaises(ValueError):
            CampaignLedger.initialize(self.root / "invalid", self.evidence, {"development": 9})
        with self.assertRaises(ValueError):
            money("0.0000000001")
        start = b'data: {"type":"message_start","message":{"usage":{"input_tokens":10,"output_tokens":0}}}\n'
        self.assertIsNone(response_usage(start + b'data: {"type":"message_delta","usage":{}}\ndata: {"type":"message_stop"}\n', True))

    def test_unpriced_usage_and_malformed_streams_cannot_release_reservations(self):
        usage = {"input_tokens": 10, "output_tokens": 20, "server_tool_use": {"web_search_requests": 1}}
        self.assertTrue(unpriced_usage(usage))
        self.assertIsNone(usage_cost_nanos(usage))
        ident = self.ledger.reserve("development", "run", money("1"))
        self.ledger.freeze("unpriced fixture")
        self.assertFalse(self.ledger.snapshot()["requests"][ident]["settled"])
        with self.assertRaises(ValueError):
            self.ledger.reserve("reserved", "run2", money("1"))
        start = b'data: {"type":"message_start","message":{"usage":{"input_tokens":10,"output_tokens":0}}}\n'
        delta = b'data: {"type":"message_delta","usage":{"output_tokens":20}}\n'
        stop = b'data: {"type":"message_stop"}\n'
        self.assertIsNone(response_usage(start + delta + stop + delta, True))
        self.assertIsNone(response_usage(start + delta + delta.replace(b'20', b'10') + stop, True))
        self.assertEqual(response_usage(start + delta + stop, True)["output_tokens"], 20)

    def test_earlier_usage_evidence_cannot_be_overwritten(self):
        def stream(initial, final):
            return b"\n".join(b"data: " + json.dumps(event).encode() for event in [
                {"type": "message_start", "message": {"usage": initial}},
                {"type": "message_delta", "usage": final}, {"type": "message_stop"}])
        initial = {"input_tokens": 10, "output_tokens": 0,
                   "server_tool_use": {"web_search_requests": 1}}
        final = {"output_tokens": 20, "server_tool_use": {"web_search_requests": 0}}
        observed = response_usage(stream(initial, final), True)
        self.assertTrue(unpriced_usage(observed))
        self.assertIsNone(usage_cost_nanos(observed))
        initial = {"input_tokens": 10, "output_tokens": 0, "cache_creation_input_tokens": 100,
                   "cache_creation": {"ephemeral_1h_input_tokens": 100}}
        final = {"output_tokens": 20, "cache_creation": {"ephemeral_5m_input_tokens": 100}}
        self.assertIsNone(response_usage(stream(initial, final), True))
        initial = {"input_tokens": -10, "output_tokens": 0}
        self.assertIsNone(response_usage(stream(initial, {"input_tokens": 10, "output_tokens": 20}), True))

    def test_live_broker_requires_shared_accounting(self):
        with self.assertRaisesRegex(ValueError, "shared campaign"):
            Broker("fixture-key", self.root / "broker")

    def test_output_ceiling_configuration_and_request_refusals_reserve_nothing(self):
        before = (self.path / "ledger.jsonl").read_bytes()
        with Broker("synthetic", self.root / "outputs", upstream="http://127.0.0.1:1/never-contacted",
                    campaign=self.path, allocation="development") as broker:
            for invalid in [True, False, 4096.0, "8192", None, 0, -1, 8193]:
                with self.subTest(configuration=invalid), self.assertRaises(ValueError):
                    broker.add_run("invalid", max_output_tokens=invalid)
            self.assertNotIn("invalid", broker.runs)
            cases = [("default", {}, 8192), ("opt-in-over", {"max_output_tokens": 8192}, 8193),
                     ("zero", {"max_output_tokens": 8192}, 0),
                     ("bool", {"max_output_tokens": 8192}, True),
                     ("float", {"max_output_tokens": 8192}, 1.5),
                     ("string", {"max_output_tokens": 8192}, "8192"),
                     ("byte-limit", {"max_output_tokens": 8192, "max_request_bytes": 32}, 8192)]
            with patch.object(broker.campaign, "reserve", wraps=broker.campaign.reserve) as reserve:
                for name, options, tokens in cases:
                    with self.subTest(request=name):
                        endpoint = broker.add_run(name, **options)
                        payload = json.dumps({"model": "claude-opus-5-5", "max_tokens": tokens}).encode()
                        with self.assertRaises(urllib.error.HTTPError) as rejected:
                            urllib.request.urlopen(urllib.request.Request(endpoint, payload), timeout=3)
                        self.assertEqual(rejected.exception.code, 400)
                        broker.close_run(name)
                reserve.assert_not_called()
            self.assertEqual(broker.runs["default"]["max_output_tokens"], 4096)
            self.assertEqual(broker.records, [])
            self.assertEqual(broker.total, 0)
        self.assertEqual((self.path / "ledger.jsonl").read_bytes(), before)

    def test_opted_in_output_reserves_actual_request_and_preserves_unknown_usage(self):
        for index, (ceiling, tokens, usage) in enumerate([
                (4096, 4096, {"input_tokens": 3, "output_tokens": 2}),
                (8192, 8192, {"input_tokens": 3, "output_tokens": 6000}),
                (8192, 32, {"input_tokens": 3, "output_tokens": 2}),
                (8192, 8192, None)]):
            with self.subTest(ceiling=ceiling, tokens=tokens, known=usage is not None):
                directory = self.root / f"output-{index}"
                campaign = self.root / f"output-ledger-{index}"
                ledger = CampaignLedger.initialize(campaign, self.evidence, {"development": "8"})
                observed = []
                class Upstream(http.server.BaseHTTPRequestHandler):
                    def log_message(self, *_): pass
                    def do_POST(self):
                        raw = self.rfile.read(int(self.headers["Content-Length"]))
                        saved = json.loads((directory / "broker.json").read_text())
                        observed.append((raw, saved["records"][-1], ledger.snapshot()))
                        body = json.dumps({"usage": usage}).encode()
                        self.send_response(200)
                        self.send_header("Content-Length", str(len(body)))
                        self.end_headers(); self.wfile.write(body)
                server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Upstream)
                thread = threading.Thread(target=server.serve_forever, daemon=True); thread.start()
                try:
                    with Broker("synthetic", directory, upstream=f"http://127.0.0.1:{server.server_port}",
                                campaign=campaign, allocation="development") as broker:
                        endpoint = broker.add_run("fixture", max_output_tokens=ceiling, max_request_bytes=144000)
                        payload = json.dumps({"model": "claude-opus-5-5", "max_tokens": tokens}).encode()
                        with urllib.request.urlopen(urllib.request.Request(endpoint, payload), timeout=3) as response:
                            response.read()
                        if usage is None:
                            with self.assertRaisesRegex(RuntimeError, "accounting did not settle"):
                                broker.close_run("fixture")
                            later = broker.add_run("later", max_output_tokens=8192)
                            with self.assertRaises(urllib.error.HTTPError):
                                urllib.request.urlopen(urllib.request.Request(later, payload), timeout=3)
                        else:
                            broker.close_run("fixture")
                        self.assertEqual(len(observed), 1)
                        raw, intent, snapshot = observed[0]
                        self.assertEqual(raw, payload)
                        self.assertEqual(intent["max_output_tokens"], ceiling)
                        self.assertEqual(intent["max_tokens"], tokens)
                        self.assertEqual(broker.runs["fixture"]["max_request_bytes"], 144000)
                        # Frozen rates: conservative $8 input and $20 output per million.
                        reservation = (len(payload) + 32768) * 8000 + tokens * 20000
                        request = next(iter(snapshot["requests"].values()))
                        self.assertEqual(request["reserved_nanos"], reservation)
                        self.assertFalse(request["settled"])
                        final = ledger.snapshot()
                        request = next(iter(final["requests"].values()))
                        expected = usage_cost_nanos(usage) if usage is not None else reservation
                        self.assertEqual(final["accounted_nanos"], money("2") + expected)
                        self.assertEqual(request["settled"], usage is not None)
                        row = json.loads((directory / "broker.json").read_text())["records"][0]
                        self.assertEqual(row["max_output_tokens"], ceiling)
                        self.assertEqual(row["accounting_settled"], usage is not None)
                        self.assertEqual(money(str(row["charged_usd"])), expected)
                finally:
                    server.shutdown(); server.server_close(); thread.join()

    def test_admission_refusal_persists_without_upstream_attempt(self):
        payload = json.dumps({"model": "claude-opus-5-5", "max_tokens": 4096,
                              "messages": [{"role": "user", "content": "fixture"}]}).encode()
        self.ledger.reserve("development", "earlier", money("4"))
        for kind, budget, campaign in [("local_budget", 0.01, None),
                                       ("shared_campaign", 10, self.path)]:
            with self.subTest(kind=kind), Broker("synthetic", self.root / kind, budget,
                    upstream="http://127.0.0.1:1/never-contacted", campaign=campaign,
                    allocation="development") as broker:
                endpoint = broker.add_run("fixture")
                with self.assertRaises(urllib.error.HTTPError) as rejected:
                    urllib.request.urlopen(urllib.request.Request(endpoint, payload,
                        {"Content-Type": "application/json"}), timeout=5)
                self.assertEqual(rejected.exception.code, 400)
                self.assertEqual(broker.admission_refusal("fixture")["kind"], kind)
                broker.close_run("fixture")
                self.assertEqual(broker.records, [])
                self.assertEqual(broker.total, 0)
                saved = json.loads((self.root / kind / "broker.json").read_text())
                self.assertEqual(saved["admission_refusals"]["fixture"]["kind"], kind)

    def test_no_http_dispatch_before_durable_campaign_reservation(self):
        calls = []

        class Upstream(http.server.BaseHTTPRequestHandler):
            def log_message(self, *_):
                pass

            def do_POST(self):
                self.rfile.read(int(self.headers["Content-Length"]))
                snapshot = CampaignLedger(self_test.path).snapshot()
                calls.append(snapshot["requests"])
                body = b'{"usage":{"input_tokens":10,"output_tokens":20}}'
                self.send_response(200)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

        self_test = self
        server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Upstream)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            with Broker("fixture-key", self.root / "broker", upstream=f"http://127.0.0.1:{server.server_port}",
                        campaign=self.path, allocation="development") as broker:
                endpoint = broker.add_run("one", max_attempts=3)
                payload = json.dumps({"model": "claude-opus-5-5", "max_tokens": 32}).encode()

                def request():
                    return urllib.request.urlopen(urllib.request.Request(endpoint, data=payload), timeout=3)

                with patch.object(broker.campaign, "reserve", side_effect=OSError("injected storage fault")):
                    with self.assertRaises(urllib.error.HTTPError):
                        request()
                self.assertEqual(calls, [])
                with request() as result:
                    result.read()
                broker.close_run("one")
                self.assertTrue(broker.records[0]["accounting_settled"])
                self.assertEqual(len(calls), 1)
                observed = next(iter(calls[0].values()))
                self.assertFalse(observed["settled"])
                self.assertGreater(observed["reserved_nanos"], 0)
                self.assertEqual(self.ledger.snapshot()["accounted_nanos"], money("2") + 440000)
        finally:
            server.shutdown(); server.server_close(); thread.join()

    def test_unsettled_response_stops_same_and_subsequent_runs(self):
        cases = [None, {"input_tokens": 10},
                 {"input_tokens": 10, "output_tokens": 20, "server_tool_use": {"web_search_requests": 1}},
                 {"input_tokens": 10, "output_tokens": 20}]
        for index, usage in enumerate(cases):
            with self.subTest(case=index):
                calls = []

                class Upstream(http.server.BaseHTTPRequestHandler):
                    def log_message(self, *_):
                        pass

                    def do_POST(self):
                        calls.append(self.rfile.read(int(self.headers["Content-Length"])))
                        body = json.dumps({"usage": usage}).encode()
                        self.send_response(200)
                        self.send_header("Content-Length", str(len(body)))
                        self.end_headers()
                        self.wfile.write(body)

                campaign = self.root / f"unsettled-{index}"
                ledger = CampaignLedger.initialize(campaign, self.evidence, {"development": "8"})
                server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Upstream)
                thread = threading.Thread(target=server.serve_forever, daemon=True)
                thread.start()
                try:
                    directory = self.root / f"broker-{index}"
                    with Broker("fixture-key", directory, upstream=f"http://127.0.0.1:{server.server_port}",
                                campaign=campaign, allocation="development") as broker:
                        endpoint = broker.add_run("first", max_attempts=3)
                        payload = json.dumps({"model": "claude-opus-5-5", "max_tokens": 32}).encode()
                        fault = (patch.object(broker.campaign, "settle", side_effect=OSError("injected flush failure"))
                                 if index == 3 else nullcontext())
                        with fault:
                            with urllib.request.urlopen(urllib.request.Request(endpoint, payload), timeout=3) as response:
                                response.read()
                            # Keep the injected settlement fault installed until
                            # both admission and close observe the accounting boundary.
                            for target, run_id in [(endpoint, "first"), (broker.add_run("next"), "next")]:
                                with self.assertRaises(urllib.error.HTTPError) as rejected:
                                    urllib.request.urlopen(urllib.request.Request(target, payload), timeout=3)
                                self.assertEqual(rejected.exception.code, 400)
                                self.assertEqual(broker.admission_refusal(run_id)["kind"], "unsettled_accounting")
                            with self.assertRaisesRegex(RuntimeError, "reservation retained"):
                                broker.close_run("first")
                            self.assertEqual(len(calls), 1)
                            self.assertEqual(len(broker.records), 1)
                            self.assertFalse(broker.records[0]["accounting_settled"])
                            snapshot = ledger.snapshot()
                            request, = snapshot["requests"].values()
                            self.assertFalse(request["settled"])
                            self.assertEqual(request["amount_nanos"], request["reserved_nanos"])
                            saved = json.loads((directory / "broker.json").read_text())
                            self.assertFalse(saved["records"][0]["accounting_settled"])
                finally:
                    server.shutdown(); server.server_close(); thread.join()


    def accounting_boundary(self, *, usage, new_run=False, close_waiting=False, expire=False, final_save_failure=False):
        """Hold the first complete body before accounting; synchronize the next admission."""
        calls = []
        parsing, release, waiting = threading.Event(), threading.Event(), threading.Event()

        class Upstream(http.server.BaseHTTPRequestHandler):
            def log_message(self, *_):
                pass

            def do_POST(self):
                calls.append(self.rfile.read(int(self.headers["Content-Length"])))
                body = json.dumps({"usage": usage}).encode()
                self.send_response(200)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

        def pause_usage(body, streaming):
            if not parsing.is_set():
                parsing.set()
                if not release.wait(5):
                    raise AssertionError("usage barrier was not released")
            return response_usage(body, streaming)

        server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Upstream)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            with Broker("fixture-key", self.root / "barrier-broker", campaign=self.path,
                        allocation="development", upstream=f"http://127.0.0.1:{server.server_port}") as broker:
                endpoint = broker.add_run("first", max_attempts=3)
                target = broker.add_run("next") if new_run else endpoint
                payload = json.dumps({"model": "claude-opus-5-5", "max_tokens": 32}).encode()
                original_wait = broker.settled.wait
                original_save = broker._save
                wake_results = []
                save_failed = threading.Event()

                def observe_wait(timeout=None):
                    waiting.set()
                    notified = original_wait(timeout)
                    wake_results.append(notified)
                    return notified

                def fail_final_save():
                    if final_save_failure and not save_failed.is_set() and any(
                            not row["active"] for row in broker.records):
                        save_failed.set()
                        raise OSError("injected final broker flush failure")
                    return original_save()

                def request(url):
                    try:
                        with urllib.request.urlopen(urllib.request.Request(url, payload), timeout=3) as response:
                            response.read()
                            return response.status
                    except urllib.error.HTTPError as response:
                        response.read()
                        return response.code

                timeout = (patch.object(broker_module, "SETTLEMENT_TIMEOUT_SECONDS", 0.1 if expire else 0.5)
                           if expire or final_save_failure else nullcontext())
                with patch.object(broker_module, "response_usage", side_effect=pause_usage), \
                     patch.object(broker.settled, "wait", side_effect=observe_wait), \
                     patch.object(broker, "_save", side_effect=fail_final_save):
                    try:
                        self.assertEqual(request(endpoint), 200)
                        self.assertTrue(parsing.wait(3), "first handler never reached the accounting barrier")
                        with ThreadPoolExecutor(max_workers=1) as pool, timeout:
                            future = pool.submit(request, target)
                            try:
                                self.assertTrue(waiting.wait(3), "next admission did not wait for prior accounting")
                                with broker.lock:
                                    self.assertEqual(len(broker.records), 1)
                                    self.assertEqual(len(calls), 1)
                                    self.assertTrue(broker.records[0]["active"])
                                    self.assertFalse(broker.records[0]["accounting_settled"])
                                if close_waiting:
                                    broker.close_run("next")
                                if not expire:
                                    release.set()
                                status = future.result(timeout=3)
                            finally:
                                release.set()
                        expected = 403 if close_waiting else 400 if expire or usage is None or final_save_failure else 200
                        self.assertEqual(status, expected)
                        expected_calls = 2 if expected == 200 else 1
                        self.assertEqual(len(calls), expected_calls)
                        if final_save_failure:
                            self.assertTrue(save_failed.is_set())
                            self.assertTrue(wake_results[0], "waiter reached deadline instead of receiving finalization notification")
                            self.assertTrue(broker.records[0]["accounting_settled"])
                            with self.assertRaisesRegex(RuntimeError, "broker evidence storage failed"):
                                broker.close_run("first")
                            saved = json.loads((broker.output / "broker.json").read_text())
                            self.assertEqual(saved["storage_failure"], broker.storage_failure)
                            self.assertEqual(saved["storage_failure"]["error"], "OSError")
                            self.assertEqual(broker.admission_refusal("first")["kind"], "broker_storage")
                            ledger_row, = self.ledger.snapshot()["requests"].values()
                            self.assertTrue(ledger_row["settled"])
                            self.assertEqual(ledger_row["amount_nanos"], usage_cost_nanos(usage))
                        elif usage is None:
                            with self.assertRaisesRegex(RuntimeError, "reservation retained"):
                                broker.close_run("first")
                        else:
                            broker.close_run("first")
                        if new_run:
                            broker.close_run("next")
                        self.assertEqual(len(self.ledger.snapshot()["requests"]), expected_calls)
                    finally:
                        release.set()
        finally:
            release.set()
            server.shutdown(); server.server_close(); thread.join()

    def test_known_usage_waits_then_next_request_proceeds(self):
        self.accounting_boundary(usage={"input_tokens": 10, "output_tokens": 20})

    def test_missing_usage_rejects_waiting_same_run(self):
        self.accounting_boundary(usage=None)

    def test_missing_usage_rejects_waiting_new_run(self):
        self.accounting_boundary(usage=None, new_run=True)

    def test_closed_run_is_rechecked_after_accounting_wait(self):
        self.accounting_boundary(usage={"input_tokens": 10, "output_tokens": 20}, new_run=True, close_waiting=True)

    def test_accounting_wait_timeout_dispatches_nothing(self):
        self.accounting_boundary(usage={"input_tokens": 10, "output_tokens": 20}, expire=True)

    def test_final_storage_failure_notifies_waiter_and_preserves_known_charge(self):
        self.accounting_boundary(usage={"input_tokens": 10, "output_tokens": 20}, final_save_failure=True)


if __name__ == "__main__":
    unittest.main()
