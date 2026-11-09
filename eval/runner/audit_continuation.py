#!/usr/bin/env python3
"""Independently audit completed Lean continuation runs without executing candidates.

Reconstructs raw history and active requests from framed observations, checks
summary provenance across actual runner checkpoints, and reconciles the broker
ledger. This does not assess the factual fidelity of generated summary text.
"""
import argparse
from decimal import Decimal
import hashlib
import json
from pathlib import Path
import re

from lean_json import AuditError, require, compact, _loads
from request_evidence import audit_request_evidence

SUMMARY_INSTRUCTION = (
    "Create a compact continuation summary of the preceding coding-agent context. Preserve the user's objective and constraints, repository facts, changes made, test results, unresolved failures, relevant paths, and next steps. Distinguish observed facts from guesses. Do not call tools or continue the task. Return only the summary as text.")

APPLICATION_SUMMARY_INSTRUCTION = (
    "Create a compact continuation summary of the preceding agent context. Preserve the user's objective and constraints, observed facts and their sources, actions taken, checks performed, unresolved failures, relevant identifiers, and next steps. Distinguish observed facts from guesses. Do not call tools or continue the task. Return only the summary as text.")

# Fixed protocol messages, checked independently of the candidate executable.
REPAIR_TEXT = {
    "invalidBatch": "[Harness validation feedback] The previous response's complete tool batch was rejected. No calls from that response executed. Return a new complete batch using unique call IDs, documented tools and fields, valid argument types and bounds, and safe relative paths. Each edit requires exact nonempty old text and the full 64-character expectedSha256 from a current file read; never use a placeholder or shortened hash. Request another read first if needed.",
    "truncated": "[Harness validation feedback] The previous response was truncated. No calls from that response executed. Return a smaller complete response with fewer or shorter tool calls. Do not assume that any proposed edit ran.",
    "malformed": "[Harness validation feedback] The previous response was incomplete or malformed. No calls from that response executed. Return a smaller complete response using the documented message and tool schemas.",
}
APPLICATION_INVALID_BATCH = "[Harness validation feedback] The previous response's complete tool batch was rejected. No calls from that response executed. Return a new complete batch using unique call IDs, documented tools and fields, valid argument types and bounds, and the documented application constraints. Read or query current information first when an operation requires it."

TIMEOUT_TEXT = "Command time limit reached; the sandboxed attempt has stopped. Partial effects may remain. Inspect the workspace and retained output before requesting more work."
TIMEOUT_SKIPPED_TEXT = "not executed: previous command timed out; inspect its partial effects before requesting more work"
CANCELLED_CALL_TEXT = "Not executed: the turn was cancelled before this call was dispatched."


def repair_message(kind, schema=5):
    text = APPLICATION_INVALID_BATCH if schema == 7 and kind == "invalidBatch" else REPAIR_TEXT[kind]
    return {"role": "user", "content": [{"type": "text", "text": text}]}


def repair_kind(message, schema=5):
    return next((kind for kind in REPAIR_TEXT if message == repair_message(kind, schema)), None)


def check_response_repairs(state, user_turns=()):
    if state["schemaVersion"] < 4:
        return 0
    count, limit = state.get("responseRepairs"), state["config"].get("maxResponseRepairs")
    require(type(count) is int and type(limit) is int and 0 <= count <= limit,
            "response-repair allowance differs")
    # A trusted follow-up may quote the exact fixed feedback. It is not a
    # repaired provider response; the declared turn records account for it.
    quoted = sum(repair_kind({"role": "user", "content": [text_block(task)]},
                            state["schemaVersion"]) is not None for task in user_turns)
    require(isinstance(state.get("history"), list) and count == sum(
        repair_kind(message, state["schemaVersion"]) is not None for message in state["history"][1:]) - quoted,
        "response-repair counter differs from accepted feedback")
    require(count <= state["modelAttempts"], "response repairs exceed model attempts")
    return count


def read_json(path):
    require(path.stat().st_size <= 64 * 1024 * 1024, "audit input exceeds supported size")
    return _loads(path.read_text())


def read_lines(path):
    require(path.stat().st_size <= 64 * 1024 * 1024, "audit input exceeds supported size")
    text = path.read_text()
    require(text.endswith("\n"), "completed run contains an incomplete final record")
    # JSONL is delimited by ASCII LF, not Unicode NEL/line/paragraph separators.
    return [_loads(line) for line in text.split("\n")[:-1]]


def schema7_context(directory, inspection, initial, plan=None):
    """Bind this coding evaluator to one installed application and explicit plan.

    Exact schema bytes come from the frozen proxy export, not a second Python
    schema definition. Compiled replay remains responsible for application
    decoding/policy and the identity of that export with the installed app.
    """
    require(initial.get("application") == inspection.get("application") == "coding" and
            type(initial.get("applicationVersion")) is int and
            type(inspection.get("applicationVersion")) is int and
            initial["applicationVersion"] == inspection.get("applicationVersion") == 1,
            "unsupported or changed application identity")
    state = inspection["state"]
    require(not inspection.get("interruptedStorage", False), "schema7 journal storage is incomplete")
    require(type(state.get("turn")) is int and state["turn"] >= 0 and state.get("grant") is None,
            "invalid final turn or retained approval")
    if plan is None:
        plan = read_json(directory.parent / "plan.json")
    require(type(plan.get("task_context_version")) is int and plan["task_context_version"] == 4,
            "schema7 requires explicit task_context_version4")
    path = directory.parent / "schemas.json"
    require(path.stat().st_size <= 1024 * 1024 and
            hashlib.sha256(path.read_bytes()).hexdigest() == plan.get("tool_schemas_sha256"),
            "frozen coding schema export missing or changed")
    schemas = read_json(path)
    require(isinstance(schemas, list) and schemas, "invalid coding schema export")
    tasks = plan.get("user_turns", [])
    require(isinstance(tasks, list) and all(isinstance(task, str) and task.strip() and
            len(task.encode()) <= state["config"]["maxContextBytes"] for task in tasks),
            "invalid declared user turns")
    return schemas, tasks


def checked_user_turn(record, terminal, pending, turn, models, config, tasks):
    require(terminal is not None and tag(terminal) in ["final", "cancelled"] and pending is None,
            "user turn follows an unsettled or ineligible boundary")
    require(type(record.get("turn")) is int and record["turn"] == turn + 1 and
            turn < len(tasks) and record.get("task") == tasks[turn],
            "undeclared, reordered or changed user turn")
    require(models < config["maxModelAttempts"], "user turn exceeds cumulative model allowance")
    return turn + 1


def text_block(text):
    return {"type": "text", "text": text}


def tag(value):
    if isinstance(value, str):
        return value
    require(isinstance(value, dict) and len(value) == 1, "invalid typed observation or phase")
    return next(iter(value))


def paired(messages):
    require(bool(messages) and messages[0]["role"] == "user", "context lacks leading user message")
    pending = []
    for message in messages:
        if message["role"] == "assistant":
            require(not pending, "context contains an unresolved preceding tool batch")
            pending = [block["id"] for block in message["content"] if block["type"] == "tool_use"]
            require(len(pending) == len(set(pending)), "context contains duplicate tool-call identities")
        else:
            require(message["role"] == "user", "context contains unsupported role")
            ids, text_seen = [], False
            for block in message["content"]:
                if block["type"] == "text":
                    text_seen = True
                else:
                    require(block["type"] == "tool_result" and not text_seen, "context tool-result ordering differs")
                    ids.append(block["tool_use_id"])
            require(ids == pending, "context contains unmatched or reordered tool results")
            pending = []
    require(not pending, "context ends with an unresolved tool batch")


def budget_message(config, model_reservations, tool_dispatches, version=2):
    """Explicitly versioned request-only notice; counters include this intent."""
    require(type(version) is int and version in [2, 3, 4], "unsupported budget notice version")
    for key in ["maxModelAttempts", "maxToolCalls", "maxOutputTokens"]:
        require(type(config.get(key)) is int and config[key] >= 0,
                "task budget notice requires natural-number frozen limits")
    models = max(0, config["maxModelAttempts"] - model_reservations)
    tools = max(0, config["maxToolCalls"] - tool_dispatches)
    timeout_notice = ""
    if version in [3, 4]:
        require(type(config.get("operationTimeoutMs")) is int and config["operationTimeoutMs"] >= 0,
                "command time-limit notice requires natural-number frozen operationTimeoutMs")
        noun = "operation" if version == 4 else "command"
        timeout_notice = (f"Configured {noun} time limit: {config['operationTimeoutMs']} ms; cleanup may take additional time. "
                          "The remaining invocation deadline may shorten this limit. "
                          f"An interrupted {noun} may have partial effects; inspect them before continuing. "
                          "Prefer focused checks that fit the time limit. ")
    text = (f"[Harness limits] After this request, at most {models} further model requests and {tools} tool executions remain. "
            "Model requests include task responses, summaries, retries, and response repairs. "
            f"This response is capped at {config['maxOutputTokens']} output tokens. "
            + timeout_notice +
            "Inspecting tool results and then responding requires another model request. "
            "These limits do not grant permission.")
    return {"role": "user", "content": [text_block(text)]}


def timeout_result(config, partial, existing):
    """Schema5's bounded error result; no wrapper exit/hash grants authority."""
    maximum = config.get("maxToolOutputBytes")
    require(type(maximum) is int and maximum >= 0, "invalid frozen timeout output bound")
    require(partial is None or isinstance(partial, dict), "invalid timeout partial result")
    partial = partial if partial is not None else {"text": "", "artifacts": []}
    require(isinstance(partial.get("text"), str) and isinstance(partial.get("artifacts"), list),
            "invalid timeout partial output")
    def bounded(text):
        return text.encode("utf-8")[:maximum].decode("utf-8", errors="ignore")
    result = {"text": bounded(TIMEOUT_TEXT + "\n" + partial["text"]),
              "exitCode": None, "sha256": None, "artifacts": partial["artifacts"]}
    offered, updated, error = result["artifacts"], list(existing), None
    if len(offered) > 2:
        error = "tool returned too many artifact references"
    else:
        for artifact in offered:
            valid = (isinstance(artifact, dict) and isinstance(artifact.get("id"), str) and
                     re.fullmatch(r"a-[0-9a-f]{64}", artifact["id"]) is not None and
                     isinstance(artifact.get("sha256"), str) and
                     re.fullmatch(r"[0-9a-f]{64}", artifact["sha256"]) is not None and
                     artifact.get("label") in ["output", "stdout", "stderr"] and
                     type(artifact.get("storedBytes")) is int and type(artifact.get("totalBytes")) is int and
                     0 <= artifact["storedBytes"] <= artifact["totalBytes"] and
                     artifact["storedBytes"] <= config["maxArtifactBytes"] and
                     type(artifact.get("truncated")) is bool and
                     artifact["truncated"] == (artifact["storedBytes"] < artifact["totalBytes"]))
            if not valid:
                error = "invalid artifact metadata"
                break
            prior = next((ref for ref in updated if ref["id"] == artifact["id"]), None)
            if prior is not None and prior != artifact:
                error = "artifact identity changed"
                break
            if prior is None:
                if len(updated) >= 1024 or sum(ref["storedBytes"] for ref in updated) + artifact["storedBytes"] > config["maxSessionArtifactBytes"]:
                    error = "session artifact allowance exhausted"
                    break
                updated.append(artifact)
    if error is not None:
        result["artifacts"] = []
        result["text"] = bounded("Artifact references rejected: " + error + "\n" + result["text"])
        updated = existing
    return result, updated


def audit_run(directory, broker, plan):
    context_version = plan.get("task_context_version", 1)
    require(type(context_version) is int and context_version in [1, 2, 3, 4],
            "unsupported plan task_context_version")
    result = read_json(directory / "result.json")
    checker = result.get("checker", {})
    if result.get("qualification_version") == 3:
        # Raw v3 success is pending independent review, which itself requires this
        # audit. Recompute these prerequisite facts without depending on that
        # later decision or trusting the copied artifact/normal summary flags.
        require(type(result.get("exit_code")) is int and result["exit_code"] == 0 and
                checker.get("resolved") is True and
                checker.get("additional_proof_integrity", True) is True,
                "task did not finish normally with an independent checker pass")
    else:
        require(result.get("success") is True and checker.get("passed", checker.get("resolved")) is True,
                "task did not finish successfully with an independent checker pass")
    require(not result.get("infrastructure_error") and not result.get("timed_out"),
            "run has an infrastructure error or timeout")
    require(result.get("replay_matches") is True, "recorded offline replay did not match")
    inspection = read_json(directory / "inspection.json")
    state = inspection["state"]
    schema = state["schemaVersion"]
    require(type(schema) is int and schema in [2, 3, 4, 5, 7] and not inspection["pending"] and inspection["terminal"],
            "session is incompatible, pending, or nonterminal")
    frames = read_lines(directory / "sessions/session/journal.jsonl")
    require(bool(frames), "empty journal")
    previous = ""
    for index, frame in enumerate(frames):
        base = {key: frame[key] for key in ["v", "seq", "previous", "record"]}
        require(frame["v"] == 1 and frame["seq"] == index and frame["previous"] == previous,
                f"invalid frame sequence {index}")
        require(hashlib.sha256(compact(base).encode()).hexdigest() == frame["checksum"],
                f"invalid frame checksum {index}")
        previous = frame["checksum"]
    records = [frame["record"] for frame in frames]
    initial = records[0]
    require(initial["kind"] == "initial" and initial["schema"] == schema, "invalid initial record")
    require(initial["implementation"] == plan["binary_sha256"], "binary identity differs from plan")
    require(initial["config"] == state["config"], "configuration changed during continuation")
    require(initial["session"] == state["sessionId"], "session identity changed")
    config = initial["config"]
    schemas, user_turns = schema7_context(directory, inspection, initial, plan) if schema == 7 else (None, [])
    require(schema == 7 or context_version != 4, "context version4 requires schema7")
    history = [{"role": "user", "content": [text_block(initial["task"])]}]
    view, pending = None, None
    summaries = state["summaries"]
    accepted_rows, model_intents, tool_intents, seen = [], [], [], []
    artifacts = []
    outstanding, handled, skipped = [], [], []
    timed_out_tools = 0
    inputs = outputs = unknown = expected_id = 0
    model_usage = []
    repairs = 0
    terminal_seen, terminal, turn = False, None, 0
    terminals, turn_events, event_turns = [], [], {}
    for record in records[1:]:
        require(type(record["id"]) is int and record["id"] == expected_id, "operation order differs from replay")
        if schema == 7 and record["kind"] == "user_turn":
            require(not outstanding, "user turn has unresolved tool calls")
            turn = checked_user_turn(record, terminal, pending, turn, len(model_intents), config, user_turns)
            history.append({"role": "user", "content": [text_block(record["task"])]})
            paired(history)
            expected_id += 1
            turn_events.append((expected_id, turn, {"task": record["task"]}))
            terminal_seen, terminal = False, None
            continue
        require(not terminal_seen, "operation after terminal without declared user turn")
        event_turns[(record["id"], record["kind"])] = turn
        if record["kind"] == "terminal":
            require(pending is None, "terminal outcome has an unresolved operation")
            terminal = record["outcome"]
            terminals.append((expected_id, turn, terminal))
            terminal_seen = True
            continue
        if record["kind"] == "intent":
            require(pending is None, "second intent before completion")
            pending = record["action"]
            if pending["kind"] == "model":
                if schema in [5, 7]:
                    require(not outstanding, "model requested before the admitted tool batch was resolved")
                request = pending["request"]
                model_intents.append((record["id"], request))
                require(request["system"] == config["instructions"] and request["model"] == config["model"],
                        "request changed model or instructions")
                require(request["maxTokens"] == config["maxOutputTokens"], "request changed output allowance")
                require(request["purpose"] in ["task", "summary"], "unknown model purpose")
                if schema == 7:
                    require(request.get("tools") == (schemas if request["purpose"] == "task" else []),
                            "request changed application tool schemas")
                paired(request["messages"])
                require(len(compact(request).encode()) + 16384 <= config["maxContextBytes"],
                        "request exceeded the frozen context allowance")
                if request["purpose"] == "task":
                    expected = history if view is None else [view["summary"]] + history[view["sourceEnd"]:]
                    if artifacts:
                        expected = [{"role": "user", "content": [text_block(
                            "Retained tool output artifacts (use artifact with an ID and byte range to read):\n" +
                            compact(artifacts))]}] + expected
                    if context_version in [2, 3, 4]:
                        expected = expected + [budget_message(config, len(model_intents), len(tool_intents), context_version)]
                    require(request["messages"] == expected, f"task context reconstruction differs at {record['id']}")
            elif pending["kind"] == "tool":
                if schema in [5, 7]:
                    require(outstanding and outstanding[0]["id"] == pending["call"]["id"],
                            "tool dispatch is skipped, duplicated, or out of admitted order")
                tool_intents.append((record["id"], pending["call"]))
            else:
                require(pending["kind"] in ["control", "wait"], "unsupported approval or effect in unattended gate")
            continue
        require(record["kind"] == "completion" and pending is not None, "completion without matching intent")
        observation = record["observation"]
        if pending["kind"] == "model":
            request = pending["request"]
            # Replay checks the core's full argument-validation decision. This
            # independent pass checks its recorded feedback, eligibility, count,
            # subsequent context and absence of dispatched rejected calls.
            next_message = state["history"][len(history)] if len(history) < len(state["history"]) else None
            repair = repair_kind(next_message, schema) if schema >= 4 and request["purpose"] == "task" else None
            if repair:
                outcome = tag(observation)
                eligible = (outcome == "failure" and observation["failure"]["kind"] == "malformed"
                            if repair == "malformed" else outcome == "success" and
                            observation["success"]["response"]["stop"] ==
                            ("maxTokens" if repair == "truncated" else "toolUse"))
                # Transient failures append no history. The next retained
                # message can belong to a later repaired response, so consume
                # feedback only when this observation has the matching class.
                if not eligible:
                    repair = None
            if repair:
                require(repairs < config["maxResponseRepairs"] and
                        len(model_intents) < config["maxModelAttempts"], "response repair exceeds admission budget")
            if tag(observation) == "success":
                response = observation["success"]["response"]
                if repair != "truncated":
                    calls = [{"id": block["id"], "name": block["name"], "input": block["input"]}
                             for block in response["content"] if block["type"] == "tool_use"]
                    text = "".join(block["text"] for block in response["content"] if block["type"] == "text")
                    require(calls == response["calls"] and text == response["text"], "normalized response disagrees with content")
                usage = response["usage"]
                if usage is None:
                    unknown += 1
                    model_usage.append(None)
                else:
                    require(all(type(usage.get(key)) is int and usage[key] >= 0
                                for key in ["inputTokens", "outputTokens"]), "invalid known core usage")
                    inputs += usage["inputTokens"]
                    outputs += usage["outputTokens"]
                    model_usage.append((usage["inputTokens"], usage["outputTokens"]))
                if request["purpose"] == "summary":
                    require(len(accepted_rows) < len(summaries), "summary completion has no retained record")
                    saved = summaries[len(accepted_rows)]
                    require(saved["response"] == response, "retained summary differs from its completion")
                    source = saved["plan"]
                    start = 0 if view is None else view["sourceEnd"]
                    prior = None if view is None else view["summary"]
                    require(source["sourceStart"] == start and source["previousSummary"] == prior,
                            "summary source does not continue the previous active view")
                    require(start < source["sourceEnd"] <= len(history), "summary source range is invalid")
                    expected = ([prior] if prior is not None else []) + history[start:source["sourceEnd"]]
                    require(request["messages"][:-1] == expected,
                            f"summary source reconstruction differs at {record['id']}")
                    instruction = APPLICATION_SUMMARY_INSTRUCTION if schema == 7 else SUMMARY_INSTRUCTION
                    require(request["messages"][-1] == {"role": "user", "content": [text_block(instruction)]},
                            "summary-purpose instruction changed")
                    require(response["stop"] == "endTurn" and response["calls"] == [] and response["text"],
                            "retained summary is incomplete or attempted tools")
                    require(len(response["text"].encode()) <= config["maxSummaryBytes"], "summary exceeds allowance")
                    view = {"sourceEnd": source["sourceEnd"], "summary": {"role": "user", "content": [
                        text_block("Continuation summary (may be incomplete):\n" + response["text"])]}}
                    accepted_rows.append(record["id"])
                elif not repair:
                    require(response["stop"] in ["toolUse", "endTurn"], "task response did not complete normally")
                    history.append({"role": "assistant", "content": response["content"]})
                    seen.extend(call["id"] for call in response["calls"])
                    if schema in [5, 7]:
                        outstanding = list(response["calls"])
            else:
                require(tag(observation) in ["failure", "interrupted", "uncertain"], "unknown model observation")
                unknown += 1
                model_usage.append(None)
            if repair:
                history.append(repair_message(repair, schema))
                repairs += 1
        elif pending["kind"] == "tool":
            kind = tag(observation)
            require(kind in (["success", "failure", "timedOut"] if schema in [5, 7] else ["success", "failure"]),
                    "unresolved or interrupted tool in continuation gate")
            if schema in [5, 7]:
                handled.append(outstanding.pop(0)["id"])
            if kind == "success":
                tool_result = observation["success"]["result"]
                if schema >= 3:
                    offered = tool_result["artifacts"]
                    require(len(offered) <= 2, "tool offered too many artifacts")
                    for artifact in offered:
                        require(re.fullmatch(r"a-[0-9a-f]{64}", artifact["id"]) is not None and
                                re.fullmatch(r"[0-9a-f]{64}", artifact["sha256"]) is not None and
                                artifact["label"] in ["output", "stdout", "stderr"], "invalid artifact metadata")
                        require(0 <= artifact["storedBytes"] <= artifact["totalBytes"] and
                                artifact["storedBytes"] <= config["maxArtifactBytes"] and
                                artifact["truncated"] == (artifact["storedBytes"] < artifact["totalBytes"]),
                                "artifact bounds or truncation differ")
                        existing = next((ref for ref in artifacts if ref["id"] == artifact["id"]), None)
                        require(existing is None or existing == artifact, "artifact identity changed")
                        if existing is None:
                            artifacts.append(artifact)
                    require(len(artifacts) <= 1024 and sum(ref["storedBytes"] for ref in artifacts) <=
                            config["maxSessionArtifactBytes"], "artifact registry exceeds frozen allowance")
                content = compact(tool_result)
                is_error = tool_result["exitCode"] is not None and tool_result["exitCode"] != 0
            elif kind == "timedOut":
                require(config.get("executionProfile") == "bubblewrap" and
                        tag(pending["call"]["operation"]) == "runProcess",
                        "invalid settled-timeout tool or execution profile")
                require(isinstance(observation["timedOut"], dict) and "partialResult" in observation["timedOut"],
                        "invalid typed timeout observation")
                tool_result, artifacts = timeout_result(config, observation["timedOut"]["partialResult"], artifacts)
                content, is_error = compact(tool_result), True
                timed_out_tools += 1
            else:
                content, is_error = observation["failure"]["message"], True
            block = {"type": "tool_result", "tool_use_id": pending["call"]["id"],
                     "content": content, "is_error": is_error}
            if history[-1]["role"] == "user":
                history[-1]["content"].append(block)
            else:
                history.append({"role": "user", "content": [block]})
            if kind == "timedOut":
                for call in outstanding:
                    history[-1]["content"].append({"type": "tool_result", "tool_use_id": call["id"],
                                                 "content": TIMEOUT_SKIPPED_TEXT, "is_error": True})
                    handled.append(call["id"])
                    skipped.append(call["id"])
                outstanding = []
        elif schema == 7 and pending["kind"] == "control" and observation.get("cancelled") is True:
            for call in outstanding:
                block = {"type": "tool_result", "tool_use_id": call["id"],
                         "content": CANCELLED_CALL_TEXT, "is_error": True}
                if history[-1]["role"] == "user":
                    history[-1]["content"].append(block)
                else:
                    history.append({"role": "user", "content": [block]})
                handled.append(call["id"])
                skipped.append(call["id"])
            outstanding = []
        expected_id += 1
        pending = None
    require(terminal_seen and pending is None, "journal did not finish")
    require(tag(state["phase"]) == "stopped" and state["phase"]["stopped"]["outcome"] == terminal,
            "terminal outcome differs from inspected state")
    if schema == 7:
        require(state["turn"] == turn == len(user_turns), "user-turn count differs from frozen schedule")
    require(len(accepted_rows) == len(summaries), "retained summary has no completion")
    require(history == state["history"], "authoritative history differs from independent observation reconstruction")
    require(repairs == check_response_repairs(state, user_turns), "response repair reconstruction differs")
    if schema >= 3:
        require(artifacts == state["artifacts"], "artifact registry differs from completed observations")
    paired(history)
    require(view == state["activeView"] and state["pendingSummary"] is None, "final active view differs")
    require(seen == state["seenCallIds"] and len(seen) == len(set(seen)), "tool identities changed or duplicated")
    require((not outstanding and handled == seen) if schema in [5, 7] else
            [call["id"] for _, call in tool_intents] == seen,
            "admitted tool calls were omitted, duplicated, or reordered")
    require(state["modelAttempts"] == len(model_intents) == result["model_attempts"], "model reservation count differs")
    require(state["toolDispatches"] == len(tool_intents) == result["tool_dispatches"], "tool dispatch count differs")
    require(state["knownInputTokens"] == inputs and state["knownOutputTokens"] == outputs, "known token ledger differs")
    require(state["unknownUsage"] == unknown and state["nextId"] == expected_id, "unknown usage or operation count differs")
    rows = read_lines(directory / ("events.jsonl" if (directory / "events.jsonl").exists() else "events.log"))
    def event_payload(value):
        if schema >= 3 and len(compact(value).encode()) > 32768:
            return {"omitted": True, "reason": "event payload exceeds 32768 bytes; inspect the journal"}
        return value
    expected_events = [(row["id"], row["kind"], event_payload(row["action"] if row["kind"] == "intent" else row["observation"]))
                       for row in records[1:] if row["kind"] in ["intent", "completion"]]
    observed_events = [(row["operation"], row["event"], row["data"]) for row in rows
                       if row["event"] in ["intent", "completion"]]
    require(observed_events == expected_events, "structured events differ from durable observations")
    if schema == 7:
        require(all(type(row.get("turn")) is int and
                    row["turn"] == event_turns.get((row["operation"], row["event"]))
                    for row in rows if row["event"] in ["intent", "completion"]),
                "structured event turn differs from journal")
    finished = [row for row in rows if row["event"] == "finished"]
    require([(row["operation"], row.get("turn", 0), row["data"]) for row in finished] ==
            [(operation, index, event_payload(outcome)) for operation, index, outcome in terminals],
            "finished event differs from journal outcome")
    if schema == 7:
        require(all(type(row.get("turn")) is int for row in finished), "finished event lacks turn identity")
        require([(row["operation"], row.get("turn"), row["data"]) for row in rows if row["event"] == "user_turn"] ==
                turn_events, "user-turn event differs from journal")
    require(all(row.get("outputLossIncidents", 0) == 0 for row in rows), "structured event output was lost")
    suspensions = [row for row in rows if row["event"] == "suspended"]
    checkpoints = result["durable_checkpoints"]
    require(len(suspensions) == len(checkpoints), "checkpoint/event count differs")
    post_summary_restarts = []
    for suspended, checkpoint in zip(suspensions, checkpoints):
        operation, phase = suspended["operation"], tag(suspended["phase"])
        require(operation == checkpoint["nextId"], "checkpoint operation differs")
        if schema == 7:
            index = sum(row["kind"] == "user_turn" and row["id"] < operation for row in records[1:])
            require(type(checkpoint.get("turn")) is int and type(suspended.get("turn")) is int and
                    checkpoint["turn"] == suspended["turn"] == index, "checkpoint turn identity differs")
        require(checkpoint["modelAttempts"] == sum(i < operation for i, _ in model_intents) +
                (phase in ["model", "summary"]), "checkpoint model reservation differs")
        require(checkpoint["toolDispatches"] == sum(i < operation for i, _ in tool_intents) +
                (phase == "tool"), "checkpoint tool reservation differs")
        if any(i < operation for i in accepted_rows) and any(
                i >= operation and request["purpose"] == "task" for i, request in model_intents):
            post_summary_restarts.append(operation)
    resource_lines = (directory / "resources.jsonl").read_text().splitlines()
    invocations = [json.loads(line) for line in resource_lines if line.startswith("{")]
    require(len(invocations) == len(checkpoints) + len(terminals), "separate invocation count differs from checkpoints and turns")
    if all("exit_code" in invocation for invocation in invocations):
        end_events = [row for row in rows if row["event"] in ["suspended", "finished"]]
        expected_exits = [75 if row["event"] == "suspended" else
                          130 if tag(row["data"]) == "cancelled" else 0 for row in end_events]
        require([invocation["exit_code"] for invocation in invocations] == expected_exits,
                "durable suspension/final invocation status differs")
    else:
        require(not user_turns, "multi-turn invocations require explicit exit codes")
        require(sum("Command exited with non-zero status 75" in line for line in resource_lines) == len(checkpoints),
                "durable suspension exit count differs")
    charges = [row for row in broker["records"] if row["run_id"] == directory.name]
    require(len(charges) == len(model_intents) == result["provider_attempts"], "provider/model call count differs")
    request_evidence = audit_request_evidence([request for _, request in model_intents], charges,
        required_version=plan.get("request_evidence_version", broker.get("request_evidence_version")))
    if schema >= 4 or any("attempt" in charge for charge in charges):
        require(all(type(charge.get("attempt")) is int and charge["attempt"] == index
                    for index, charge in enumerate(charges, 1)),
                "provider attempts are missing, duplicated or reordered")
    require(all(not row.get("active") for row in charges), "provider accounting remains active")
    require(sum(row["usage"] is None for row in charges) == result["unknown_usage_requests"], "provider unknown count differs")
    require(abs(sum(Decimal(str(row["charged_usd"])) for row in charges) -
                Decimal(str(result["accounted_usd"]))) < Decimal("1e-9"), "run cost differs from broker")
    require(len(model_usage) == len(charges), "core/provider usage attempt counts differ")
    provider_only = core_only = 0
    for core, charge in zip(model_usage, charges):
        provider = charge["usage"]
        if provider is not None:
            require(all(type(provider.get(key)) is int and provider[key] >= 0
                        for key in ["input_tokens", "output_tokens"]), "invalid known provider usage")
        if core is not None and provider is not None:
            require(core == (provider["input_tokens"], provider["output_tokens"]),
                    "provider usage differs from corresponding journal completion")
        elif core is None and provider is not None:
            provider_only += 1
        elif core is not None:
            core_only += 1
    prices = broker["prices_per_million"]
    for charge in charges:
        usage = charge["usage"]
        if usage is None:
            expected_cost = Decimal(str(charge["reserved_usd"]))
        else:
            expected_cost = (usage["input_tokens"] * Decimal(str(prices["input"])) + usage["output_tokens"] * Decimal(str(prices["output"])) +
                             usage.get("cache_read_input_tokens", 0) * Decimal(str(prices["cache_read"])) +
                             usage.get("cache_creation_input_tokens", 0) * Decimal(str(prices["cache_write"]))) / 1_000_000
        require(abs(Decimal(str(charge["charged_usd"])) - expected_cost) < Decimal("1e-9"), "request cost differs from frozen price ledger")
    require(len(accepted_rows) >= 2 and bool(post_summary_restarts),
            "strict gate requires two accepted summaries and subsequent continuation across a process restart")
    return {"run": directory.name, "status": "passed", "task_context_version": context_version, "successful_summaries": len(accepted_rows),
            "summary_operation_ids": accepted_rows, "restart_operations": [row["operation"] for row in suspensions],
            "post_summary_restart_operations": post_summary_restarts, "process_invocations": len(invocations),
            "model_attempts": len(model_intents), "tool_dispatches": len(tool_intents), "unknown_usage": unknown,
            "response_repairs": repairs, "unknown_core_known_provider": provider_only,
            "user_turns": turn + 1, "declared_followups": len(user_turns),
            "known_core_unknown_provider": core_only,
            "request_evidence": request_evidence,
            "raw_history_messages": len(history), "journal_frames": len(frames), "accounted_usd": float(result["accounted_usd"]),
            **({"timed_out_tools": timed_out_tools, "skipped_tool_call_ids": skipped} if schema in [5, 7] else {})}


def audit_directory(directory):
    plan, broker = read_json(directory / "plan.json"), read_json(directory / "broker.json")
    require(plan["engines"] == ["lean"] and plan["yield_after"] > 0, "not a Lean continuation cohort")
    results = []
    for child in sorted(directory.iterdir()):
        if not child.is_dir() or not (child / "config.json").exists():
            continue
        try:
            results.append(audit_run(child, broker, plan))
        except (AuditError, OSError, ValueError, KeyError, TypeError, StopIteration) as error:
            results.append({"run": child.name, "status": "failed", "reason": str(error)})
    expected = len(plan["tasks"]) * len(plan["tracks"]) * plan["repetitions"]
    return {"schema_version": 1, "cohort": directory.name, "binary_sha256": plan["binary_sha256"],
            "audit": "independent framed-observation reconstruction; generated summary fidelity not assessed",
            "expected_runs": expected, "audited_runs": len(results),
            "passed": len(results) == expected and all(row["status"] == "passed" for row in results),
            "runs": results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        report = audit_directory(args.directory)
    except (AuditError, OSError, ValueError, KeyError, TypeError) as error:
        report = {"passed": False, "reason": str(error)}
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
