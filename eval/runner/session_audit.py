"""Read-only checks for completed schema-3/4/5 and schema-7 coding runs.

Replay/inspect equality alone is not independent evidence: both use the core's
replay implementation. Framing, counts, usage, terminal events and retained output bytes
are checked separately here. This is not a model-answer correctness checker.
"""
import hashlib
import json
from pathlib import Path
import re

from audit_continuation import (AuditError, check_response_repairs, checked_user_turn, compact,
                               read_lines, require, schema7_context, tag)
from request_evidence import audit_request_evidence


def _usage_counts(usage, input_key, output_key, label):
    require(isinstance(usage, dict), label + " usage is not an object")
    counts = tuple(usage.get(key) for key in (input_key, output_key))
    require(all(type(value) is int and value >= 0 for value in counts),
            label + " usage lacks nonnegative input/output counts")
    return counts


def completed_session(directory, inspected, replayed, charges, *, normal, request_evidence_version=None, plan=None):
    directory = Path(directory)
    require(inspected == replayed, "inspect and replay differ")
    state = inspected["state"]
    schema = state["schemaVersion"]
    require(type(schema) is int and schema in [3, 4, 5, 7] and inspected["terminal"] and not inspected["pending"]
            and not inspected["interruptedStorage"], "completed session is incompatible or unsettled")
    frames = read_lines(directory / "sessions/session/journal.jsonl")
    previous = ""
    for sequence, frame in enumerate(frames):
        base = {key: frame[key] for key in ["v", "seq", "previous", "record"]}
        require(frame["v"] == 1 and frame["seq"] == sequence and frame["previous"] == previous,
                "journal frame ordering differs")
        require(hashlib.sha256(compact(base).encode()).hexdigest() == frame["checksum"],
                "journal frame checksum differs")
        previous = frame["checksum"]
    records = [frame["record"] for frame in frames]
    require(records and records[0]["kind"] == "initial" and records[0]["schema"] == state["schemaVersion"],
            "missing or incompatible initial schema record")
    require(records[0]["config"] == state["config"] and records[0]["session"] == state["sessionId"],
            "session configuration or identity changed")
    schemas, user_turns = schema7_context(directory, inspected, records[0], plan) if schema == 7 else (None, [])
    pending, operation, models, tools = None, 0, [], []
    terminal, turn, terminals, turn_events = None, 0, [], []
    model_usage, inputs, outputs, unknown = [], 0, 0, 0
    for record in records[1:]:
        require(type(record["id"]) is int and record["id"] == operation, "unexpected operation order")
        kind = record["kind"]
        if schema == 7 and kind == "user_turn":
            turn = checked_user_turn(record, terminal, pending, turn, len(models), state["config"], user_turns)
            operation += 1
            turn_events.append((operation, turn, {"task": record["task"]}))
            terminal = None
            continue
        require(terminal is None, "operation after terminal without declared user turn")
        if kind == "intent":
            require(pending is None, "two intents without completion")
            pending = record["action"]
            if pending["kind"] == "model":
                if schema == 7:
                    request = pending["request"]
                    require(request.get("purpose") in ["task", "summary"] and
                            request.get("tools") == (schemas if request["purpose"] == "task" else []),
                            "request changed application tool schemas")
                models.append(pending)
            if pending["kind"] == "tool":
                tools.append(pending["call"]["id"])
        elif kind == "completion":
            require(pending is not None, "completion without intent")
            if pending["kind"] == "model":
                observation = record["observation"]
                outcome = tag(observation)
                require(outcome in {"success", "failure", "interrupted", "uncertain"},
                        "unknown model completion")
                usage = observation["success"]["response"]["usage"] if outcome == "success" else None
                if usage is None:
                    unknown += 1
                    model_usage.append(None)
                else:
                    counts = _usage_counts(usage, "inputTokens", "outputTokens", "core")
                    inputs += counts[0]
                    outputs += counts[1]
                    model_usage.append(counts)
            pending = None
            operation += 1
        elif kind == "terminal":
            require(pending is None, "terminal record has an unresolved operation")
            terminal = record["outcome"]
            terminals.append((operation, turn, terminal))
        else:
            require(False, "administrative intervention in unattended public run")
    require(terminal is not None and tag(state["phase"]) == "stopped"
            and state["phase"]["stopped"]["outcome"] == terminal and state["nextId"] == operation,
            "terminal state differs from recorded outcome")
    if schema == 7:
        require(state["turn"] == turn == len(user_turns), "user-turn count differs from frozen schedule")
    config = state["config"]
    require(state["modelAttempts"] == len(models) <= config["maxModelAttempts"], "model reservation mismatch")
    require(state["toolDispatches"] == len(tools) <= config["maxToolCalls"], "tool reservation mismatch")
    require(state["knownInputTokens"] == inputs and state["knownOutputTokens"] == outputs,
            "known token ledger differs from model completions")
    require(state["unknownUsage"] == unknown, "unknown token ledger differs from model completions")
    repairs = check_response_repairs(state, user_turns)
    require(len(tools) == len(set(tools)) and set(tools) <= set(state["seenCallIds"]),
            "tool calls duplicated or not admitted")
    require(len(charges) <= len(models) and all(not row.get("active") for row in charges),
            "provider attempts exceed reservations or remain unsettled")
    if normal:
        require(tag(terminal) == "final" and len(charges) == len(models),
                "normal finish lacks final answer or complete provider-attempt accounting")
    provider_usage = []
    for index, charge in enumerate(charges, 1):
        require(type(charge.get("attempt")) is int and charge["attempt"] == index,
                "provider attempts are missing, duplicated or reordered")
        usage = charge.get("usage")
        provider_usage.append(None if usage is None else
                              _usage_counts(usage, "input_tokens", "output_tokens", "provider"))
    # A local preflight/transport failure can reserve a core attempt without
    # reaching the broker. Do not invent positional alignment across that gap.
    aligned = len(charges) == len(models)
    request_evidence = audit_request_evidence([model.get("request", {}) for model in models], charges,
        required_version=request_evidence_version)
    paired_known = core_only = provider_only = 0
    if aligned:
        for core, provider in zip(model_usage, provider_usage):
            if core is not None and provider is not None:
                require(core == provider, "provider usage differs from corresponding model completion")
                paired_known += 1
            elif core is not None:
                core_only += 1
            elif provider is not None:
                provider_only += 1
    events = read_lines(directory / "events.log")
    finished = [event for event in events if event.get("event") == "finished"]
    require(len(finished) == len(terminals), "finished event differs")
    for event, (operation_id, turn_id, outcome) in zip(finished, terminals):
        if schema == 7:
            require(type(event.get("turn")) is int, "finished event lacks turn identity")
        require(event["operation"] == operation_id and event.get("turn", 0) == turn_id,
                "finished event differs")
        if not (isinstance(event["data"], dict) and event["data"].get("omitted")):
            require(event["data"] == outcome, "finished event outcome differs")
    if schema == 7:
        require([(event["operation"], event.get("turn"), event["data"]) for event in events
                 if event.get("event") == "user_turn"] == turn_events, "user-turn event differs from journal")
    require(all(event.get("outputLossIncidents", 0) == 0 for event in events), "events were lost")
    retained = 0
    for artifact in state["artifacts"]:
        require(re.fullmatch(r"a-[0-9a-f]{64}", artifact["id"]) is not None, "invalid artifact identity")
        blob = directory / "sessions/session/artifacts" / (artifact["id"] + ".blob")
        require(not blob.is_symlink() and blob.is_file() and blob.stat().st_nlink == 1,
                "artifact is missing, linked or irregular")
        size = blob.stat().st_size
        require(size == artifact["storedBytes"] <= config["maxArtifactBytes"], "artifact length differs")
        require(hashlib.sha256(blob.read_bytes()).hexdigest() == artifact["sha256"], "artifact hash differs")
        metadata = blob.with_suffix(".json")
        require(not metadata.is_symlink() and metadata.is_file() and metadata.stat().st_nlink == 1
                and metadata.stat().st_size <= 4096, "artifact metadata is missing, linked or oversized")
        require(json.loads(metadata.read_text()) == artifact, "artifact metadata differs from admitted reference")
        retained += size
    require(retained <= config["maxSessionArtifactBytes"], "retained artifact allowance exceeded")
    return {"passed": True, "journal_frames": len(frames), "model_attempts": len(models),
            "response_repairs": repairs,
            "user_turns": turn + 1, "declared_followups": len(user_turns),
            "tool_dispatches": len(tools), "verified_artifacts": len(state["artifacts"]),
            "verified_artifact_bytes": retained,
            "request_evidence": request_evidence,
            "usage": {"known_input_tokens": inputs, "known_output_tokens": outputs,
                      "core_unknown_attempts": unknown,
                      "provider_unknown_attempts": sum(usage is None for usage in provider_usage),
                      "attempts_aligned": aligned, "matched_known_attempts": paired_known,
                      "known_core_unknown_provider": core_only if aligned else None,
                      "unknown_core_known_provider": provider_only if aligned else None},
            "scope": "core replay plus independent frame/count/usage/event/artifact checks; no task-quality inference"}
