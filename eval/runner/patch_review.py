"""Offline v3 qualification of an immutable run; this never executes a candidate.

Reviews are trusted evaluator evidence, authored outside the agent workspace.
Hashes bind the review to the saved result and patch; they do not authenticate
the reviewer or prove that the review is correct. Original results stay intact.
"""
import argparse
import hashlib
import json
from pathlib import Path

VERSION = 3
TASK_CONSTRAINTS = (
    "Complete the requested behavior within the task workspace. You may add regression tests, including in existing "
    "test files, and update expected outputs when the requested behavior requires it. Explain changes to existing "
    "tests. Do not delete, disable, skip, or weaken unrelated tests or assertions, change fixed theorem statements, "
    "or bypass checks. Do not alter protected grading infrastructure."
)
QUALIFICATION_RULE = (
    "Official artifact checks pass, normal finish, settled execution/accounting, Lean session integrity, "
    "and independent patch review bound to the exact saved result and candidate patch. Test-file changes "
    "alone neither qualify nor disqualify a result. Original result remains pending until separate review."
)
REVIEW_CHECKS = (
    "requested_behavior_addressed",
    "preexisting_test_changes_justified",
    "no_unrelated_test_weakening_or_deletion",
    "no_checker_bypass",
    "protected_infrastructure_intact",
)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def automated_checks(record):
    """These are necessary conditions, never an automatic patch approval."""
    checker = record.get("checker", {})
    terminal = record.get("pi_terminal_observation") or {}
    pi_finished = (record.get("engine") != "pi" or (
        terminal.get("normalFinish") is True and terminal.get("stopReason") == "stop"
        and not terminal.get("error") and not record.get("pi_terminal_observation_error")
        and type(record.get("tool_dispatches")) is int and record["tool_dispatches"] >= 0))
    return {
        "normal_finish": type(record.get("exit_code")) is int and record["exit_code"] == 0 and pi_finished,
        "artifact_pass": checker.get("resolved") is True and checker.get("additional_proof_integrity", True) is True,
        "session_integrity": record.get("engine") != "lean" or record.get("session_integrity", {}).get("passed") is True,
        "settled_execution": not any(record.get(key) for key in (
            "not_run", "infrastructure_error", "cleanup_failure", "cleanup_unsettled", "accounting_unsettled", "admission_refused")),
        "known_usage": type(record.get("unknown_usage_requests")) is int and record["unknown_usage_requests"] == 0,
        "continuation_integrity": not record.get("requires_continuation_audit") or (
            record.get("sustained_gate_passed") is True and record.get("continuation_audit", {}).get("status") == "passed"),
        **({"initial_task_request": type(record["request_evidence_version"]) is int and
            record["request_evidence_version"] == 1 and
            record.get("initial_task_request_evidence", {}).get("passed") is True}
           if "request_evidence_version" in record else {}),
    }


def evidence(run_dir):
    run_dir = Path(run_dir)
    raw = (run_dir / "result.json").read_bytes()
    record = json.loads(raw)
    if record.get("qualification_version") != VERSION:
        raise ValueError("v3 qualification cannot reinterpret an older frozen result")
    if record.get("engine") not in {"lean", "pi"}:
        raise ValueError("unsupported candidate engine")
    patch_hash = digest((run_dir / "candidate.patch").read_bytes())
    if record.get("candidate_patch_sha256") != patch_hash:
        raise ValueError("candidate patch differs from the artifact graded by this run")
    for field in ("run_id", "user_task_sha256"):
        if not isinstance(record.get(field), str) or not record[field]:
            raise ValueError("missing run/task identity")
    return {"run_id": record["run_id"], "result_sha256": digest(raw),
            "candidate_patch_sha256": patch_hash, "user_task_sha256": record["user_task_sha256"],
            "candidate_tree": record.get("workspace_snapshot", {}).get("candidate_tree"),
            "automated_checks": automated_checks(record)}


def review_template(run_dir):
    return {"qualification_version": VERSION, "evidence": evidence(run_dir),
            "reviewer": "", "independent_of_candidate": None, "decision": "pending",
            "rationale": "", "checks": {key: None for key in REVIEW_CHECKS}}


def qualify(run_dir, review):
    expected = evidence(run_dir)
    if review.get("qualification_version") != VERSION or review.get("evidence") != expected:
        raise ValueError("review does not bind this exact run and candidate patch")
    if review.get("decision") not in {"approve", "reject"}:
        raise ValueError("an explicit approve/reject decision is required")
    if review.get("independent_of_candidate") is not True:
        raise ValueError("an independent evaluator review is required")
    if not all(isinstance(review.get(key), str) and review[key].strip() for key in ("reviewer", "rationale")):
        raise ValueError("reviewer and rationale must be recorded")
    checks = review.get("checks")
    if not isinstance(checks, dict) or set(checks) != set(REVIEW_CHECKS) or any(type(value) is not bool for value in checks.values()):
        raise ValueError("each patch-review criterion requires an explicit boolean finding")
    return {"qualification_version": VERSION, "evidence": expected,
            "qualified_success": review["decision"] == "approve" and all(checks.values())
                and all(expected["automated_checks"].values()),
            "review": review,
            "scope": "Separate prospective qualification; original result, upstream verdict and artifact unchanged."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["template", "qualify"])
    parser.add_argument("run", type=Path)
    parser.add_argument("--review", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.mode == "qualify" and args.review is None:
        parser.error("qualify requires --review authored independently of the candidate")
    try:
        if args.mode == "template":
            result = review_template(args.run)
        else:
            raw = args.review.read_bytes()
            result = qualify(args.run, json.loads(raw))
            result["review_sha256"] = digest(raw)
        # A new file prevents accidental replacement of raw results or reviews.
        with args.output.open("x") as stream:
            stream.write(json.dumps(result, indent=2) + "\n")
    except (ValueError, OSError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
