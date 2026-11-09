#!/usr/bin/env python3
"""Independently audit completed Lean continuation runs without executing candidates.

Reconstructs raw history and active requests from framed observations, checks
summary provenance across actual runner checkpoints, and reconciles the broker
ledger. This does not assess the factual fidelity of generated summary text.
"""
import argparse
import hashlib
import json
from pathlib import Path

SUMMARY_INSTRUCTION = (
    "Create a compact continuation summary of the preceding coding-agent context. Preserve the user's objective and constraints, repository facts, changes made, test results, unresolved failures, relevant paths, and next steps. Distinguish observed facts from guesses. Do not call tools or continue the task. Return only the summary as text.")


class AuditError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def compact(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def read_json(path):
    require(path.stat().st_size <= 64 * 1024 * 1024, "audit input exceeds supported size")
    return json.loads(path.read_text())


def read_lines(path):
    require(path.stat().st_size <= 64 * 1024 * 1024, "audit input exceeds supported size")
    text = path.read_text()
    require(text.endswith("\n"), "completed run contains an incomplete final record")
    return [json.loads(line) for line in text.splitlines()]


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


def audit_run(directory, broker, plan):
    result = read_json(directory / "result.json")
    require(result.get("success") is True and result.get("checker", {}).get("passed") is True,
            "task did not finish successfully with an independent checker pass")
    require(not result.get("infrastructure_error") and not result.get("timed_out"),
            "run has an infrastructure error or timeout")
    require(result.get("replay_matches") is True, "recorded offline replay did not match")
    inspection = read_json(directory / "inspection.json")
    state = inspection["state"]
    require(state["schemaVersion"] == 2 and not inspection["pending"] and inspection["terminal"],
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
    require(initial["kind"] == "initial" and initial["schema"] == 2, "invalid initial record")
    require(initial["implementation"] == plan["binary_sha256"], "binary identity differs from plan")
    require(initial["config"] == state["config"], "configuration changed during continuation")
    require(initial["session"] == state["sessionId"], "session identity changed")
    config = initial["config"]
    history = [{"role": "user", "content": [text_block(initial["task"])]}]
    view, pending = None, None
    summaries = state["summaries"]
    accepted_rows, model_intents, tool_intents, seen = [], [], [], []
    inputs = outputs = unknown = expected_id = 0
    terminal_seen = False
    for record in records[1:]:
        require(not terminal_seen and record["id"] == expected_id, "operation order differs from replay")
        if record["kind"] == "terminal":
            require(pending is None, "terminal outcome has an unresolved operation")
            require(tag(state["phase"]) == "stopped" and
                    state["phase"]["stopped"]["outcome"] == record["outcome"],
                    "terminal outcome differs from inspected state")
            terminal_seen = True
            continue
        if record["kind"] == "intent":
            require(pending is None, "second intent before completion")
            pending = record["action"]
            if pending["kind"] == "model":
                request = pending["request"]
                model_intents.append((record["id"], request))
                require(request["system"] == config["instructions"] and request["model"] == config["model"],
                        "request changed model or instructions")
                require(request["maxTokens"] == config["maxOutputTokens"], "request changed output allowance")
                require(request["purpose"] in ["task", "summary"], "unknown model purpose")
                paired(request["messages"])
                require(len(compact(request).encode()) + 16384 <= config["maxContextBytes"],
                        "request exceeded the frozen context allowance")
                if request["purpose"] == "task":
                    expected = history if view is None else [view["summary"]] + history[view["sourceEnd"]:]
                    require(request["messages"] == expected, f"task context reconstruction differs at {record['id']}")
            elif pending["kind"] == "tool":
                tool_intents.append((record["id"], pending["call"]))
            else:
                require(pending["kind"] in ["control", "wait"], "unsupported approval or effect in unattended gate")
            continue
        require(record["kind"] == "completion" and pending is not None, "completion without matching intent")
        observation = record["observation"]
        if pending["kind"] == "model":
            request = pending["request"]
            if tag(observation) == "success":
                response = observation["success"]["response"]
                calls = [{"id": block["id"], "name": block["name"], "input": block["input"]}
                         for block in response["content"] if block["type"] == "tool_use"]
                text = "".join(block["text"] for block in response["content"] if block["type"] == "text")
                require(calls == response["calls"] and text == response["text"], "normalized response disagrees with content")
                usage = response["usage"]
                if usage is None:
                    unknown += 1
                else:
                    inputs += usage["inputTokens"]
                    outputs += usage["outputTokens"]
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
                    require(request["messages"][-1] == {"role": "user", "content": [text_block(SUMMARY_INSTRUCTION)]},
                            "summary-purpose instruction changed")
                    require(response["stop"] == "endTurn" and response["calls"] == [] and response["text"],
                            "retained summary is incomplete or attempted tools")
                    require(len(response["text"].encode()) <= config["maxSummaryBytes"], "summary exceeds allowance")
                    view = {"sourceEnd": source["sourceEnd"], "summary": {"role": "user", "content": [
                        text_block("Continuation summary (may be incomplete):\n" + response["text"])]}}
                    accepted_rows.append(record["id"])
                else:
                    require(response["stop"] in ["toolUse", "endTurn"], "task response did not complete normally")
                    history.append({"role": "assistant", "content": response["content"]})
                    seen.extend(call["id"] for call in response["calls"])
            else:
                require(tag(observation) in ["failure", "interrupted", "uncertain"], "unknown model observation")
                unknown += 1
        elif pending["kind"] == "tool":
            kind = tag(observation)
            require(kind in ["success", "failure"], "unresolved or interrupted tool in continuation gate")
            if kind == "success":
                tool_result = observation["success"]["result"]
                content = compact(tool_result)
                is_error = tool_result["exitCode"] is not None and tool_result["exitCode"] != 0
            else:
                content, is_error = observation["failure"]["message"], True
            block = {"type": "tool_result", "tool_use_id": pending["call"]["id"],
                     "content": content, "is_error": is_error}
            if history[-1]["role"] == "user":
                history[-1]["content"].append(block)
            else:
                history.append({"role": "user", "content": [block]})
        expected_id += 1
        pending = None
    require(terminal_seen and pending is None, "journal did not finish")
    require(len(accepted_rows) == len(summaries), "retained summary has no completion")
    require(history == state["history"], "authoritative history differs from independent observation reconstruction")
    paired(history)
    require(view == state["activeView"] and state["pendingSummary"] is None, "final active view differs")
    require(seen == state["seenCallIds"] and len(seen) == len(set(seen)), "tool identities changed or duplicated")
    require([call["id"] for _, call in tool_intents] == seen, "admitted tool calls were omitted, duplicated, or reordered")
    require(state["modelAttempts"] == len(model_intents) == result["model_attempts"], "model reservation count differs")
    require(state["toolDispatches"] == len(tool_intents) == result["tool_dispatches"], "tool dispatch count differs")
    require(state["knownInputTokens"] == inputs and state["knownOutputTokens"] == outputs, "known token ledger differs")
    require(state["unknownUsage"] == unknown and state["nextId"] == expected_id, "unknown usage or operation count differs")
    rows = read_lines(directory / "events.jsonl")
    expected_events = [(row["id"], row["kind"], row["action"] if row["kind"] == "intent" else row["observation"])
                       for row in records[1:] if row["kind"] in ["intent", "completion"]]
    observed_events = [(row["operation"], row["event"], row["data"]) for row in rows
                       if row["event"] in ["intent", "completion"]]
    require(observed_events == expected_events, "structured events differ from durable observations")
    finished = [row for row in rows if row["event"] == "finished"]
    require(len(finished) == 1 and finished[0]["operation"] == expected_id and
            finished[0]["data"] == records[-1]["outcome"], "finished event differs from journal outcome")
    suspensions = [row for row in rows if row["event"] == "suspended"]
    checkpoints = result["durable_checkpoints"]
    require(len(suspensions) == len(checkpoints), "checkpoint/event count differs")
    post_summary_restarts = []
    for suspended, checkpoint in zip(suspensions, checkpoints):
        operation, phase = suspended["operation"], tag(suspended["phase"])
        require(operation == checkpoint["nextId"], "checkpoint operation differs")
        require(checkpoint["modelAttempts"] == sum(i < operation for i, _ in model_intents) +
                (phase in ["model", "summary"]), "checkpoint model reservation differs")
        require(checkpoint["toolDispatches"] == sum(i < operation for i, _ in tool_intents) +
                (phase == "tool"), "checkpoint tool reservation differs")
        if any(i < operation for i in accepted_rows) and any(
                i >= operation and request["purpose"] == "task" for i, request in model_intents):
            post_summary_restarts.append(operation)
    resource_lines = (directory / "resources.jsonl").read_text().splitlines()
    invocations = [json.loads(line) for line in resource_lines if line.startswith("{")]
    require(len(invocations) == len(checkpoints) + 1, "separate invocation count differs from checkpoints")
    require(sum("Command exited with non-zero status 75" in line for line in resource_lines) == len(checkpoints),
            "durable suspension exit count differs")
    charges = [row for row in broker["records"] if row["run_id"] == directory.name]
    require(len(charges) == len(model_intents) == result["provider_attempts"], "provider/model call count differs")
    require(all(not row.get("active") for row in charges), "provider accounting remains active")
    require(sum(row["usage"] is None for row in charges) == result["unknown_usage_requests"], "provider unknown count differs")
    require(abs(sum(row["charged_usd"] for row in charges) - result["accounted_usd"]) < 1e-9, "run cost differs from broker")
    require(sum(row["usage"]["input_tokens"] for row in charges if row["usage"]) == inputs and
            sum(row["usage"]["output_tokens"] for row in charges if row["usage"]) == outputs,
            "provider usage differs from journal usage")
    prices = broker["prices_per_million"]
    for charge in charges:
        usage = charge["usage"]
        if usage is None:
            expected_cost = charge["reserved_usd"]
        else:
            expected_cost = (usage["input_tokens"] * prices["input"] + usage["output_tokens"] * prices["output"] +
                             usage.get("cache_read_input_tokens", 0) * prices["cache_read"] +
                             usage.get("cache_creation_input_tokens", 0) * prices["cache_write"]) / 1_000_000
        require(abs(charge["charged_usd"] - expected_cost) < 1e-9, "request cost differs from frozen price ledger")
    require(len(accepted_rows) >= 2 and bool(post_summary_restarts),
            "strict gate requires two accepted summaries and subsequent continuation across a process restart")
    return {"run": directory.name, "status": "passed", "successful_summaries": len(accepted_rows),
            "summary_operation_ids": accepted_rows, "restart_operations": [row["operation"] for row in suspensions],
            "post_summary_restart_operations": post_summary_restarts, "process_invocations": len(invocations),
            "model_attempts": len(model_intents), "tool_dispatches": len(tool_intents), "unknown_usage": unknown,
            "raw_history_messages": len(history), "journal_frames": len(frames), "accounted_usd": result["accounted_usd"]}


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
