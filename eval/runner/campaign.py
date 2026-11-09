"""Shared durable spending admission for evaluation brokers; no provider transport."""
import argparse
from contextlib import contextmanager
from decimal import Decimal
import fcntl
import hashlib
import json
import os
from pathlib import Path
import stat
import uuid

NANOS = 1_000_000_000


def money(value):
    amount = Decimal(str(value)) * NANOS
    if not amount.is_finite() or amount < 0 or amount != amount.to_integral_value():
        raise ValueError("money must be nonnegative, finite, and exact to nanodollars")
    return int(amount)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()


def natural(value):
    return type(value) is int and value >= 0


def _transfer(caps, totals, requests, frozen, record):
    source, destination = record.get("from"), record.get("to")
    amount, reason = record.get("amount_nanos"), record.get("reason")
    if (not isinstance(source, str) or not isinstance(destination, str)
            or source == destination or source not in caps or destination not in caps
            or not natural(amount) or amount == 0
            or not isinstance(reason, str) or not reason.strip() or len(reason) > 1024):
        raise ValueError("invalid campaign allocation transfer")
    if frozen or any(not request["settled"] for request in requests.values()):
        raise ValueError("allocation transfer requires an unfrozen, settled campaign")
    if amount > caps[source] - totals[source]:
        raise ValueError("allocation transfer exceeds unspent source allowance")
    caps[source] -= amount
    caps[destination] += amount


class CampaignLedger:
    """Reservations survive crashes. An incomplete ledger stops further spending.

    This is a local accounting boundary, not a provider-enforced billing cap.
    Checksums detect accidental damage, not a malicious trusted-directory writer.
    """

    def __init__(self, directory):
        self.directory = Path(directory).resolve(strict=True)
        self.path = self.directory / "ledger.jsonl"
        self.snapshot()  # Refuse missing/corrupt accounting before request admission.

    @staticmethod
    def initialize(directory, evidence, allocations):
        raw = Path(evidence).read_bytes()
        previous = json.loads(raw)
        authorized = money(previous["authorized_budget_usd"])
        spent = money(previous["total_accounted_usd"])
        amounts = {name: money(value) for name, value in allocations.items()}
        if not amounts or spent + sum(amounts.values()) > authorized:
            raise ValueError("allocations exceed the remaining authorized campaign budget")
        root = Path(directory)
        root.mkdir(mode=0o700, exist_ok=False)
        initial = {"kind": "initial", "version": 1, "authorized_nanos": authorized,
                   "prior_accounted_nanos": spent, "allocations_nanos": amounts,
                   "prior_evidence_sha256": hashlib.sha256(raw).hexdigest()}
        path = root / "ledger.jsonl"
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
        try:
            CampaignLedger._write(fd, 0, initial)
        finally:
            os.close(fd)
        parent = os.open(root, os.O_DIRECTORY | os.O_RDONLY)
        try:
            os.fsync(parent)
        finally:
            os.close(parent)
        parent = os.open(root.parent, os.O_DIRECTORY | os.O_RDONLY)
        try:
            os.fsync(parent)
        finally:
            os.close(parent)
        return CampaignLedger(root)

    @contextmanager
    def _locked(self):
        lock = os.open(self.directory / "lock", os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
        try:
            info = os.fstat(lock)
            if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
                raise ValueError("campaign lock must be an unaliased regular file")
            fcntl.flock(lock, fcntl.LOCK_EX)
            fd = os.open(self.path, os.O_RDWR | os.O_APPEND | os.O_NOFOLLOW)
            try:
                info = os.fstat(fd)
                if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1 or info.st_size > 64 * 1024 * 1024:
                    raise ValueError("invalid campaign ledger file or size")
                with os.fdopen(os.dup(fd), "rb") as source:
                    raw = source.read(64 * 1024 * 1024 + 1)
                yield fd, self._replay(raw)
            finally:
                os.close(fd)
        finally:
            os.close(lock)

    @staticmethod
    def _write(fd, sequence, payload):
        framed = {"seq": sequence, "payload": payload}
        framed["sha256"] = hashlib.sha256(canonical(framed)).hexdigest()
        data = canonical(framed) + b"\n"
        offset = 0
        while offset < len(data):
            written = os.write(fd, data[offset:])
            if written <= 0:
                raise OSError("campaign ledger write made no progress")
            offset += written
        os.fsync(fd)

    @staticmethod
    def _replay(raw):
        if not raw or not raw.endswith(b"\n"):
            raise ValueError("incomplete campaign ledger; preserve evidence and stop paid work")
        records = []
        for sequence, line in enumerate(raw.splitlines()):
            framed = json.loads(line)
            expected = hashlib.sha256(canonical({"seq": framed["seq"], "payload": framed["payload"]})).hexdigest()
            if framed["seq"] != sequence or framed["sha256"] != expected:
                raise ValueError("campaign framing/checksum mismatch")
            records.append(framed["payload"])
        initial = records[0]
        if initial.get("kind") != "initial" or initial.get("version") != 1:
            raise ValueError("unsupported campaign schema")
        caps = initial["allocations_nanos"]
        authorized, prior = initial["authorized_nanos"], initial["prior_accounted_nanos"]
        if not natural(authorized) or not natural(prior) or not isinstance(caps, dict) or not caps:
            raise ValueError("invalid initial accounting")
        if any(not isinstance(name, str) or not natural(cap) for name, cap in caps.items()) or prior + sum(caps.values()) > authorized:
            raise ValueError("invalid campaign allocations")
        requests, totals, frozen = {}, {name: 0 for name in caps}, False
        for record in records[1:]:
            if record.get("kind") == "freeze":
                if not isinstance(record.get("reason"), str) or not record["reason"]:
                    raise ValueError("invalid campaign freeze record")
                frozen = True
                continue
            if record.get("kind") == "transfer":
                _transfer(caps, totals, requests, frozen, record)
                continue
            ident, amount = record["id"], record["amount_nanos"]
            if not isinstance(ident, str) or not natural(amount):
                raise ValueError("invalid request accounting")
            if record["kind"] == "reserve":
                allocation = record["allocation"]
                if ident in requests or allocation not in caps or frozen:
                    raise ValueError("invalid campaign reservation")
                if totals[allocation] + amount > caps[allocation] or prior + sum(totals.values()) + amount > authorized:
                    raise ValueError("reservation exceeds campaign authorization")
                requests[ident] = {**record, "settled": False, "reserved_nanos": amount}
                totals[allocation] += amount
            elif record["kind"] == "settle":
                if ident not in requests or requests[ident]["settled"]:
                    raise ValueError("settlement has no unique reservation")
                request = requests[ident]
                totals[request["allocation"]] += amount - request["amount_nanos"]
                frozen |= amount > request["reserved_nanos"]
                request.update(amount_nanos=amount, settled=True, usage=record["usage"])
            else:
                raise ValueError("unknown campaign record")
        return {"next_sequence": len(records), "authorized_nanos": authorized,
                "prior_accounted_nanos": prior, "allocations_nanos": caps,
                "allocation_charged_nanos": totals, "accounted_nanos": prior + sum(totals.values()),
                "requests": requests, "frozen": frozen}

    def snapshot(self):
        with self._locked() as (_, state):
            return state

    def reserve(self, allocation, run_id, amount_nanos):
        if not natural(amount_nanos) or amount_nanos == 0 or not isinstance(run_id, str):
            raise ValueError("invalid reservation")
        with self._locked() as (fd, state):
            if state["frozen"]:
                raise ValueError("actual usage exceeded a reservation; campaign is frozen for review")
            if allocation not in state["allocations_nanos"]:
                raise ValueError("unknown campaign allocation")
            if state["allocation_charged_nanos"][allocation] + amount_nanos > state["allocations_nanos"][allocation] or state["accounted_nanos"] + amount_nanos > state["authorized_nanos"]:
                raise ValueError("shared campaign spending allowance exhausted")
            ident = uuid.uuid4().hex
            self._write(fd, state["next_sequence"], {"kind": "reserve", "id": ident,
                        "allocation": allocation, "run_id": run_id, "amount_nanos": amount_nanos})
            return ident

    def settle(self, ident, amount_nanos, usage):
        if not natural(amount_nanos) or not isinstance(usage, dict):
            raise ValueError("invalid settlement")
        with self._locked() as (fd, state):
            request = state["requests"].get(ident)
            if request is None:
                raise ValueError("unknown campaign request")
            if request["settled"]:
                if request["amount_nanos"] == amount_nanos and request["usage"] == usage:
                    return  # A durable identical settlement is safe to observe again.
                raise ValueError("request already settled differently")
            self._write(fd, state["next_sequence"], {"kind": "settle", "id": ident,
                        "amount_nanos": amount_nanos, "usage": usage})

    def freeze(self, reason):
        if not isinstance(reason, str) or not reason or len(reason) > 1024:
            raise ValueError("invalid campaign freeze reason")
        with self._locked() as (fd, state):
            if not state["frozen"]:
                self._write(fd, state["next_sequence"], {"kind": "freeze", "reason": reason})

    def transfer(self, source, destination, amount_nanos, reason):
        """Move unused allowance without changing authorization or recorded costs.

        No automatic retry: after a write/flush error, inspect the durable ledger
        before deciding whether another transfer is needed.
        """
        record = {"kind": "transfer", "from": source, "to": destination,
                  "amount_nanos": amount_nanos, "reason": reason}
        with self._locked() as (fd, state):
            _transfer(state["allocations_nanos"], state["allocation_charged_nanos"],
                      state["requests"], state["frozen"], record)
            self._write(fd, state["next_sequence"], record)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["init", "inspect"])
    parser.add_argument("directory", type=Path)
    parser.add_argument("--prior-report", type=Path)
    parser.add_argument("--allocation", action="append", default=[], help="NAME=DOLLARS")
    args = parser.parse_args()
    if args.mode == "init":
        if args.prior_report is None or not args.allocation:
            parser.error("init requires --prior-report and named --allocation amounts")
        ledger = CampaignLedger.initialize(args.directory, args.prior_report,
                                           dict(item.split("=", 1) for item in args.allocation))
    else:
        ledger = CampaignLedger(args.directory)
    print(json.dumps(ledger.snapshot(), indent=2))
