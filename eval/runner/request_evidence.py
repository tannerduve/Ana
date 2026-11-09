"""Bounded outbound request digests; no bodies, headers or credentials retained.

Version 1 hashes exact UTF-8 wire bytes and the present system/messages members
using the pinned Lean compact codec. Object-key order and equivalent decimal
spellings normalize; arrays, strings and JSON value types do not. Absent and null
members differ. This is neither universal JSON canonicalization nor proof that
an upstream service received or honored a request.
"""
from decimal import Decimal
import hashlib
import json
import re

from lean_json import AuditError, compact, require

REQUEST_EVIDENCE_VERSION = 1
CONTEXT_CODEC = "lean-json-compact-v1"
MAX_REQUEST_BYTES = 400_000
MAX_DEPTH = 128
MAX_NUMBER_DIGITS = 4096
MAX_EXPONENT = 4096
MAX_NUMERIC_WORK = 1024 * 1024
_FIELDS = ("request_evidence_version", "outbound_body_sha256", "outbound_body_bytes",
           "system_messages_sha256", "system_messages_canonicalization_version")


def parse_request(raw):
    """Strict grammar remains json.loads; this only bounds work and ambiguity."""
    require(type(raw) is bytes and 0 < len(raw) <= MAX_REQUEST_BYTES,
            "outbound request exceeds byte bound")
    text = raw.decode("utf-8", errors="strict")
    depth, quoted, escaped = 0, False, False
    for char in text:
        if quoted:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                quoted = False
        elif char == '"':
            quoted = True
        elif char in "[{":
            depth += 1
            require(depth <= MAX_DEPTH, "outbound JSON nesting exceeds bound")
        elif char in "]}":
            depth -= 1
    work = 0

    def number(token, integer=False):
        nonlocal work
        require(sum(char in "0123456789" for char in token) <= MAX_NUMBER_DIGITS,
                "outbound JSON number exceeds digit bound")
        parts = re.split("[eE]", token)
        exponent = int(parts[1]) if len(parts) == 2 else 0
        require(abs(exponent) <= MAX_EXPONENT, "outbound JSON exponent exceeds bound")
        work += sum(char in "0123456789" for char in parts[0]) + max(0, exponent)
        require(work <= MAX_NUMERIC_WORK, "outbound JSON numeric work exceeds bound")
        return int(token) if integer else Decimal(token)

    def pairs(rows):
        obj = {}
        for key, value in rows:
            require(key not in obj, "duplicate outbound JSON object key")
            obj[key] = value
        return obj

    def invalid_constant(_):
        raise AuditError("non-finite outbound JSON number")

    value = json.loads(text, parse_int=lambda token: number(token, True),
                       parse_float=number, parse_constant=invalid_constant,
                       object_pairs_hook=pairs)
    require(isinstance(value, dict), "outbound request must be an object")
    # Validate all strings/numbers, including fields outside the context digest.
    # The numeric work allowance bounds expansion by the shared compact printer.
    compact(value)
    return value


def context_digest(payload):
    value = {key: payload[key] for key in ("system", "messages") if key in payload}
    canonical = compact(value).encode("utf-8")
    return hashlib.sha256((CONTEXT_CODEC + "\n").encode() + canonical).hexdigest()


# Optional observational metadata: never an admission or generation policy.
SETTINGS_EVIDENCE_VERSION = 1
MAX_EFFORT_MARKERS = 64
_EFFORTS = frozenset({"low", "medium", "high", "xhigh", "max"})
_THINKING_TYPES = frozenset({"disabled", "enabled", "adaptive"})
_MISSING_SETTING = object()


def _setting(value, allowed=None):
    if value is _MISSING_SETTING:
        return {"state": "absent"}
    if value is None:
        return {"state": "null"}
    if allowed is not None:
        valid = type(value) is str and value in allowed
    else:
        valid = type(value) is int and 0 <= value <= 2 ** 31 - 1
    return {"state": "known", "value": value} if valid else {"state": "unrecognized"}


def _member_setting(container, key, allowed=None):
    if container is _MISSING_SETTING:
        return {"state": "absent"}
    if container is None:
        return {"state": "null_container"}
    if not isinstance(container, dict):
        return {"state": "unrecognized_container"}
    return _setting(container.get(key, _MISSING_SETTING), allowed)


def request_settings_evidence(payload):
    """Bounded allowlisted controls, not message content or effective model behavior."""
    thinking = payload.get("thinking", _MISSING_SETTING)
    output = payload.get("output_config", _MISSING_SETTING)
    markers, count = [], 0
    messages = payload.get("messages", [])
    if isinstance(messages, list):
        for index, message in enumerate(messages):
            if not isinstance(message, dict) or message.get("role") != "system" or "output_config" not in message:
                continue
            count += 1
            if len(markers) < MAX_EFFORT_MARKERS:
                markers.append({"message_index": index,
                                "effort": _member_setting(message["output_config"], "effort", _EFFORTS)})
    return {"version": SETTINGS_EVIDENCE_VERSION,
            "max_tokens": _setting(payload.get("max_tokens", _MISSING_SETTING)),
            "thinking_type": _member_setting(thinking, "type", _THINKING_TYPES),
            "thinking_budget_tokens": _member_setting(thinking, "budget_tokens"),
            "top_level_effort": _member_setting(output, "effort", _EFFORTS),
            "system_message_efforts": markers,
            "system_message_effort_count": count,
            "system_message_efforts_truncated": count > len(markers),
            "scope": "Allowlisted controls observed before dispatch; no provider interpretation or compliance claim."}


def outbound_evidence(raw):
    payload = parse_request(raw)
    return payload, {
        "request_evidence_version": REQUEST_EVIDENCE_VERSION,
        "outbound_body_sha256": hashlib.sha256(raw).hexdigest(),
        "outbound_body_bytes": len(raw),
        "system_messages_sha256": context_digest(payload),
        "system_messages_canonicalization_version": CONTEXT_CODEC,
        "request_settings": request_settings_evidence(payload),
    }


def user_text_digests(payload):
    """Indexed top-level user text only; tool-result text is deliberately excluded."""
    rows = []
    for message_index, message in enumerate(payload.get("messages", [])):
        if not isinstance(message, dict) or message.get("role") != "user":
            continue
        content = message.get("content")
        blocks = [(None, content)] if isinstance(content, str) else [
            (index, block["text"]) for index, block in enumerate(content if isinstance(content, list) else [])
            if isinstance(block, dict) and block.get("type") == "text" and isinstance(block.get("text"), str)]
        rows.extend({"message_index": message_index, "block_index": index,
                     "text_sha256": hashlib.sha256(text.encode("utf-8")).hexdigest()}
                    for index, text in blocks)
    return rows


def _check_record(charge, index):
    require(type(charge.get("attempt")) is int and charge["attempt"] == index,
            "outbound request evidence attempt order differs")
    require(type(charge.get("request_evidence_version")) is int and
            charge["request_evidence_version"] == REQUEST_EVIDENCE_VERSION,
            "missing or unsupported outbound request evidence")
    require(charge.get("system_messages_canonicalization_version") == CONTEXT_CODEC,
            "unsupported outbound context codec")
    require(all(isinstance(charge.get(key), str) and re.fullmatch("[0-9a-f]{64}", charge[key])
                for key in ["outbound_body_sha256", "system_messages_sha256"]),
            "invalid outbound request digest")
    require(type(charge.get("outbound_body_bytes")) is int and
            0 < charge["outbound_body_bytes"] <= MAX_REQUEST_BYTES and
            charge["outbound_body_bytes"] == charge.get("request_bytes"),
            "outbound request byte count differs")


def audit_initial_task(charges, expected_sha256):
    """A full task must occur in one text block in the first observed request."""
    require(isinstance(expected_sha256, str) and re.fullmatch("[0-9a-f]{64}", expected_sha256),
            "invalid expected initial task digest")
    require(charges and type(charges[0].get("attempt")) is int and charges[0]["attempt"] == 1,
            "missing first outbound request")
    first = charges[0]
    _check_record(first, 1)
    require(first.get("outbound_transport_state") == "response_observed",
            "first request has no observed upstream response; dispatch intent is not delivery")
    rows = first.get("initial_user_text_sha256")
    require(isinstance(rows, list) and all(isinstance(row, dict) and
            set(row) == {"message_index", "block_index", "text_sha256"} and
            type(row.get("message_index")) is int and row["message_index"] >= 0 and
            (row.get("block_index") is None or type(row["block_index"]) is int and row["block_index"] >= 0) and
            isinstance(row.get("text_sha256"), str) and re.fullmatch("[0-9a-f]{64}", row["text_sha256"])
            for row in rows), "missing or invalid first-request user text evidence")
    matches = [row for row in rows if row["text_sha256"] == expected_sha256]
    require(matches, "full task text is absent or altered in the first outbound request")
    return {"passed": True, "version": REQUEST_EVIDENCE_VERSION, "matching_positions": matches,
            "scope": "First-request user text only; an upstream response was observed. No later Pi context reconstruction or provider instruction-compliance claim."}


def audit_request_evidence(requests, charges, *, required_version=None):
    """Compare journal-normalized contexts, only when ordinal alignment is known.

    No full-body reconstruction is claimed: the body hash is validated metadata,
    while independent system/messages reconstruction supplies the compared value.
    A legacy record never silently becomes an evidence match.
    """
    require(required_version is None or (type(required_version) is int and
            required_version == REQUEST_EVIDENCE_VERSION), "unsupported required request evidence version")
    observed = any(any(key in charge for key in _FIELDS) for charge in charges)
    if required_version is None and not observed:
        return {"status": "unavailable_legacy", "matched_contexts": 0,
                "attempts": len(charges), "scope": "No outbound digests were retained; no transport-context equality claim."}
    require(len(requests) == len(charges), "outbound request evidence cannot align missing provider attempts")
    for index, (request, charge) in enumerate(zip(requests, charges), 1):
        _check_record(charge, index)
        require(charge["system_messages_sha256"] == context_digest(request),
                "outbound system/messages differ from corresponding journal request")
    return {"status": "matched", "version": REQUEST_EVIDENCE_VERSION,
            "canonicalization": CONTEXT_CODEC, "matched_contexts": len(charges),
            "scope": "Context digests match journal requests by ordinal; exact body digests are retained but not independently reconstructed. Broker/transport and upstream semantics remain trusted boundaries."}
