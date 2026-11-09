#!/usr/bin/env python3
"""Redact and aggregate saved public runs without model calls or regrading."""
import argparse
from collections import defaultdict
from decimal import Decimal
import hashlib
import json
from pathlib import Path


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def accounted(record, prices):
    usage = record.get("usage")
    if not isinstance(usage, dict) or not all(k in usage for k in ["input_tokens", "output_tokens"]):
        return Decimal(str(record["charged_usd"]))
    fields = {"input_tokens": "input", "output_tokens": "output",
              "cache_read_input_tokens": "cache_read", "cache_creation_input_tokens": "cache_write"}
    return sum((Decimal(usage.get(field, 0)) * Decimal(str(prices[key])) for field, key in fields.items()), Decimal(0)) / 1_000_000


def pi_tool_count(path):
    final = None
    for line in path.open(errors="replace"):
        if not line.startswith("{"):
            continue
        try:
            event = json.loads(line)
        except ValueError:
            continue
        if event.get("type") == "evaluation_end":
            final = event.get("toolDispatches")
    return final


def summarize(directories, include_unavailable=True):
    runs, plans = [], []
    unavailable = [{"task_id": "psf__requests-2317", "engine": engine, "repetition": 0,
                    "cohort": "original-preselection", "not_run": True, "provider_attempts": 0,
                    "reason": "Preflight-ineligible: changed external HTTPBIN redirect contract; no candidate grading attempted."}
                   for engine in ["lean", "pi"]] if include_unavailable else []
    total = Decimal(0)
    seen = set()
    for directory in directories:
        plan = json.loads((directory / "plan.json").read_text())
        if plan.get("qualification_version", 0) >= 3:
            raise ValueError("historical reporter cannot score v3 pending reviews; report separate qualified-result evidence")
        ledger = json.loads((directory / "broker.json").read_text())
        originals = [(path, json.loads(path.read_text())) for path in sorted(directory.glob("*/result.json"))]
        if any(row.get("qualification_version", 0) >= 3 for _, row in originals):
            raise ValueError("historical reporter cannot score v3 pending reviews; report separate qualified-result evidence")
        expected = {(task, engine, repetition) for task in plan["tasks"] for engine in plan["engines"]
                    for repetition in range(plan.get("repetition_start", 0),
                                            plan.get("repetition_start", 0) + plan["repetitions"])}
        observed = {(row["task_id"], row["engine"], row["repetition"]) for _, row in originals}
        results_path = directory / "results.json"
        skipped = [r for r in json.loads(results_path.read_text()) if r.get("not_run")] if results_path.is_file() else []
        observed |= {(r["task_id"], r["engine"], r["repetition"]) for r in skipped}
        for row in skipped:
            unavailable.append({"task_id": row["task_id"], "engine": row["engine"], "repetition": row["repetition"],
                                "cohort": plan.get("cohort") or "original-preselection", "not_run": True,
                                "provider_attempts": row["provider_attempts"], "reason": row["infrastructure_error"]})
        if observed != expected:
            raise ValueError(f"incomplete or unexpected declared batch {directory.name}: "
                             f"missing={sorted(expected - observed)}, unexpected={sorted(observed - expected)}")
        plans.append({"directory": directory.name, "plan_sha256": sha(directory / "plan.json"),
                      "ledger_sha256": sha(directory / "broker.json"),
                      "public_lock_sha256": plan["public_lock_sha256"],
                      "binary_sha256": plan["binary_sha256"], "tool_binary_sha256": plan["tool_binary_sha256"],
                      "pi_lock_sha256": plan["pi_lock_sha256"], "model": plan["model"],
                      "runner_sha256": plan.get("runner_sha256"),
                      "max_attempts": plan["max_attempts"], "max_tools": plan["max_tools"],
                      "context_bytes": plan["context_bytes"], "timeout_seconds": plan["timeout_seconds"],
                      "prices_per_million": ledger["prices_per_million"]})
        total += sum((accounted(record, ledger["prices_per_million"]) for record in ledger["records"]), Decimal(0))
        for path, original in originals:
            if original["run_id"] in seen:
                raise ValueError("duplicate run id in report inputs")
            seen.add(original["run_id"])
            checker = original.get("checker", {})
            row = {key: original.get(key) for key in ["run_id", "task_id", "benchmark", "engine", "track",
                "repetition", "exit_code", "elapsed_seconds", "provider_attempts", "accounted_usd",
                "unknown_usage_requests", "model_attempts", "tool_dispatches", "summaries", "image_digest"]}
            row["cohort"] = original.get("cohort", "additional-after-preflight-failure" if original["task_id"].startswith("django") else "original-preselection")
            row["attempt"] = original.get("attempt", 1)
            row["apt_https"] = original.get("apt_https", False)
            row["apt_main_only"] = original.get("apt_main_only", False)
            row["agent_launch_observed"] = "exit_code" in original or original.get("timed_out", False)
            row["official_resolved"] = checker.get("resolved", False)
            row["normal_exit"] = original.get("exit_code") == 0
            row["strict_qualification_noncomparable"] = original["success"]
            row["test_files_modified"] = original.get("test_files_modified", [])
            row["proof_integrity"] = checker.get("additional_proof_integrity")
            row["typed_proof_audit"] = checker.get("typed_proof_audit")
            row["infrastructure_error"] = original.get("infrastructure_error")
            row["timed_out"] = original.get("timed_out", False)
            row["result_sha256"] = sha(path)
            if original["engine"] == "pi" and (path.parent / "events.log").is_file():
                row["tool_dispatches"] = pi_tool_count(path.parent / "events.log")
            usage = [record.get("usage") for record in ledger["records"] if record["run_id"] == original["run_id"]]
            row["accounted_usd_exact"] = str(sum((accounted(record, ledger["prices_per_million"])
                for record in ledger["records"] if record["run_id"] == original["run_id"]), Decimal(0)))
            row["known_usage"] = {field: sum(u.get(field, 0) for u in usage if isinstance(u, dict))
                for field in ["input_tokens", "output_tokens", "cache_read_input_tokens", "cache_creation_input_tokens"]}
            report = checker.get("official_report", {})
            row["official_empty_patch"] = original["task_id"] in report.get("empty_patch_ids", [])
            failures = []
            for report_path in (path.parent / "verification/logs/evaluation").glob("**/report.json"):
                report_data = json.loads(report_path.read_text()).get(original["task_id"], {})
                for kind in ["FAIL_TO_PASS", "PASS_TO_PASS"]:
                    failures += report_data.get("tests_status", {}).get(kind, {}).get("failure", [])
            row["official_failed_tests"] = failures
            runs.append(row)
    groups = defaultdict(lambda: {"attempt_records": 0, "executed": 0, "setup_failures": 0, "official_resolved": 0, "normal_exits": 0,
                                  "infrastructure_failures": 0, "charged_usd": Decimal(0)})
    for row in runs:
        group = groups[(row["benchmark"], row["cohort"], row["attempt"], row["engine"])]
        group["attempt_records"] += 1
        group["executed"] += row["agent_launch_observed"]
        group["setup_failures"] += not row["agent_launch_observed"]
        group["official_resolved"] += row["official_resolved"]
        group["normal_exits"] += row["normal_exit"]
        group["infrastructure_failures"] += bool(row["infrastructure_error"])
        group["charged_usd"] += Decimal(row["accounted_usd_exact"])
    aggregated = [{"benchmark": key[0], "cohort": key[1], "attempt": key[2], "engine": key[3],
                   **{k: float(v) if isinstance(v, Decimal) else v for k, v in value.items()}}
                  for key, value in sorted(groups.items())]
    unavailable = list({(r["cohort"], r["task_id"], r["engine"], r["repetition"]): r for r in unavailable}.values())
    slots = {(r["cohort"], r["task_id"], r["engine"], r["repetition"]) for r in runs}
    initial = [r for r in runs if r["attempt"] == 1]
    retries = [r for r in runs if r["attempt"] > 1]
    return {"schema_version": 1, "label": "small public development sample; not leaderboard or parity evidence",
            "primary_score": "upstream resolved/reward; normal exit reported separately",
            "qualification_caveat": "Stored strict success additionally forbids test edits; only Lean received that extra instruction, so that qualifier is not directly comparable. Pi product uses native instructions. Review edits for actual weakening.",
            "executed_runs": sum(r["agent_launch_observed"] for r in runs),
            "execution_attempt_records": len(runs), "additional_retry_attempts": len(runs) - len(slots),
            "setup_failures": sum(not r["agent_launch_observed"] for r in runs),
            "planned_unexecuted": unavailable,
            "total_planned_run_slots": len(slots) + len(unavailable),
            "total_accounted_usd": float(total), "total_accounted_usd_exact": str(total),
            "cost_basis": "configured broker token prices and provider usage; not an independently verified invoice",
            "provenance_limitations": [{"directory": p["directory"], "limitation":
                "No runner source hash was recorded in the pre-run plan. Current source hashes cannot establish the original orchestration source."}
                for p in plans if p["runner_sha256"] is None],
            "context_policy": {"lean_estimated_context_bytes": sorted({p["context_bytes"] for p in plans}),
                               "pi": "native product context policy",
                               "common_broker_request_bytes": sorted({p["context_bytes"] + 24000 for p in plans})},
            "peak_memory": "not measured for public runs",
            "unknown_usage_requests": sum(r["unknown_usage_requests"] for r in runs),
            "upstream_resolved_runs": sum(r["official_resolved"] for r in runs),
            "normal_exits": sum(r["normal_exit"] for r in runs), "groups": aggregated,
            "initial_attempts": {"records": len(initial), "executed": sum(r["agent_launch_observed"] for r in initial),
                                 "official_resolved": sum(r["official_resolved"] for r in initial),
                                 "normal_exits": sum(r["normal_exit"] for r in initial)},
            "retry_attempts": {"records": len(retries), "executed": sum(r["agent_launch_observed"] for r in retries),
                               "official_resolved": sum(r["official_resolved"] for r in retries),
                               "normal_exits": sum(r["normal_exit"] for r in retries)},
            "plans": plans, "runs": runs}


def markdown(report):
    initial = [row for row in report["runs"] if row["attempt"] == 1]
    retries = [row for row in report["runs"] if row["attempt"] > 1]
    initial_cost = sum((Decimal(row["accounted_usd_exact"]) for row in initial), Decimal(0))
    retry_cost = sum((Decimal(row["accounted_usd_exact"]) for row in retries), Decimal(0))
    limits = "; ".join(f"{attempts} provider attempts, {tools} tools, and {seconds} agent seconds"
                       for attempts, tools, seconds in sorted({
                           (p["max_attempts"], p["max_tools"], p["timeout_seconds"]) for p in report["plans"]}))
    models = ", ".join("Claude Opus 5.5" if model == "claude-opus-5-5" else model
                       for model in sorted({p["model"] for p in report["plans"]}))
    contexts = ", ".join(f"{n:,}" for n in report["context_policy"]["lean_estimated_context_bytes"])
    request_limits = ", ".join(f"{n:,}" for n in report["context_policy"]["common_broker_request_bytes"])
    tasks = [
        ("pallets__flask-4045", "Flask blueprints", "SWE-bench Lite"),
        ("django__django-11099", "Django validators (additional)", "SWE-bench Lite"),
        ("openssl-selfsigned-cert", "Self-signed certificate", "Terminal-Bench 2.1"),
        ("prove-plus-comm", "Coq addition proof", "Terminal-Bench 2.1"),
    ]
    lines = ["# Public benchmark sample", "",
             "We compared the Lean harness with Pi on Flask blueprints, Django username validation, a self-signed certificate, "
             "and a Coq addition proof. These are **selected SWE-bench Lite tasks** graded by the official SWE-bench evaluator, "
             "plus two Terminal-Bench 2.1 tasks using upstream verifiers. Neither full suite was run; this small sample does not "
             "establish general parity.", "",
             "Original results below show **official passes / planned attempts**, including setup failures. "
             "“Finished normally” means exit code 0; it does not mean the patch passed its tests.", "",
             "| Task | Benchmark | Lean: original attempts | Pi: original attempts |",
             "| --- | --- | --- | --- |"]
    for task_id, label, benchmark in tasks:
        cells = []
        for engine in ["lean", "pi"]:
            rows = [r for r in initial if r["task_id"] == task_id and r["engine"] == engine]
            failures = sum(not r["agent_launch_observed"] for r in rows)
            cell = f"{sum(r['official_resolved'] for r in rows)}/{len(rows)}"
            if failures:
                cell += f"; {failures} setup failure"
            cells.append(cell)
        lines.append(f"| {label} | {benchmark} | {cells[0]} | {cells[1]} |")
    lines += ["| Requests redirects | SWE-bench Lite | Not run: preflight failed | Not run: preflight failed |", "",
              "Django was an additional selection made before its model runs after Requests failed preflight. Requests' HTTPBIN "
              "dependency now rejects a required redirect; both planned runs remain recorded. Coq's two setup failures occurred "
              "before model calls. After a successful baseline/reference gate with HTTPS and main-only Ubuntu package indexes, "
              "one separate rerun per engine passed. Original failures were retained.", "",
              "| Stage | Agent executions | Official passes | Finished normally | Cost |",
              "| --- | --- | --- | --- | --- |"]
    for label, stats, cost in [("Initial attempts", report["initial_attempts"], initial_cost),
                                ("Coq reruns", report["retry_attempts"], retry_cost)]:
        lines.append(f"| {label} | {stats['executed']} | {stats['official_resolved']} | {stats['normal_exits']} | ${cost:.6f} |")
    lines += [f"| Total | {report['executed_runs']} | {report['upstream_resolved_runs']} | {report['normal_exits']} | "
              f"${Decimal(report['total_accounted_usd_exact']):.6f} |", "",
              f"There were {report['total_planned_run_slots']} planned slots: {report['initial_attempts']['executed']} initial "
              f"executions, {report['setup_failures']} setup failures, and {len(report['planned_unexecuted'])} Requests exclusions. "
              f"The {report['retry_attempts']['records']} reruns add attempts, not replacements. Cost uses configured prices and provider "
              f"usage; unknown-usage requests: {report['unknown_usage_requests']}. The separate "
              "[Flask budget diagnostic](2026-11-09-flask-budget-diagnostic.md) is excluded here.", "",
              "All four runnable tasks failed unchanged baselines and passed upstream reference solutions. Official checks ran "
              "in fresh images with unchanged verifiers. The [supplemental Coq audit](2026-11-09-public-coq-audit.json) "
              "checked the required theorem type and closed assumptions for all four saved proofs; early artifacts were audited afterwards.", "",
              f"Both engines used {models} in product mode: {limits}, with 4096 output tokens. "
              "Summaries and SDK retries count as attempts. Engine order reversed on the second repetition. "
              "Product prompts, tools, and thinking defaults can differ.", "",
              f"- Lean estimates context against {contexts} bytes; Pi keeps its native context policy. Both face a separate "
              f"{request_limits}-byte broker request ceiling.",
              "- Only Lean received the extra instruction forbidding test edits. The stricter stored `success` flag is "
              "therefore not comparable; the tables use official verifier outcomes.",
              "- Elapsed time includes setup and excludes grading. Peak memory was not measured.",
              "- The first six-run plan omitted the runner-source hash. It recorded binary, tool, Pi-lock, and benchmark-lock "
              "identities; later plans also hash the runner.", "",
              "[Run JSON](2026-11-09-public-sample.json) retains individual results and hashes; "
              "[preflight history](2026-11-09-public-preflight.json) preserves setup attempts and interruptions. "
              "[Pinned assets and instructions](../PUBLIC.md) explain reproduction. Raw transcripts and private keys are omitted.", ""]
    return "\n".join(lines)


def diagnostic_markdown(report):
    attempts = ", ".join(str(n) for n in sorted({p["max_attempts"] for p in report["plans"]}))
    tools = ", ".join(str(n) for n in sorted({p["max_tools"] for p in report["plans"]}))
    seconds = ", ".join(str(n) for n in sorted({p["timeout_seconds"] for p in report["plans"]}))
    contexts = ", ".join(f"{n:,}" for n in report["context_policy"]["lean_estimated_context_bytes"])
    request_limits = ", ".join(f"{n:,}" for n in report["context_policy"]["common_broker_request_bytes"])
    lines = ["# Flask budget diagnostic", "",
             "This follow-up compared the Lean harness and Pi again on Flask's blueprint task from SWE-bench Lite, using its "
             "official evaluator. It was selected "
             "after both engines failed both original runs and is **excluded from the frozen comparison**. "
             "The binaries, task, and product prompts stayed unchanged; neither model received hidden-test findings.", "",
             f"Each engine received two new runs with **{attempts} provider attempts and {tools} tools**, doubled from 12 and 24. "
             f"The {seconds}-second agent allowance and 4096-token output ceiling stayed unchanged.", "",
             "| Engine | Run | Official result | Finished normally | Model calls | Cost |",
             "| --- | --- | --- | --- | --- | --- |"]
    for row in report["runs"]:
        outcome = "Pass" if row["official_resolved"] else "Fail"
        normal = "Yes" if row["normal_exit"] else "No"
        lines.append(f"| {row['engine'].capitalize()} | {row['repetition'] + 1} | {outcome} | {normal} | "
                     f"{row['provider_attempts']} | ${Decimal(row['accounted_usd_exact']):.6f} |")
    lines += ["", "Finished normally means exit code 0, not a correct patch. Both Lean runs finished but failed the official "
              "check: extra calls alone did not resolve this task. Pi passed once and failed once. These selected repeats "
              "do not establish a general budget effect or a harness correctness fix.", "",
              f"Total: **{report['upstream_resolved_runs']}/{report['executed_runs']} official passes**, "
              f"{report['normal_exits']} normal finishes, **${report['total_accounted_usd_exact']}** accounted cost, "
              f"and {report['unknown_usage_requests']} unknown-usage requests.", "",
              f"The original comparison's limits still apply: Lean uses a {contexts}-byte context estimator, Pi its native policy, "
              f"and both a {request_limits}-byte broker request ceiling. Only Lean received the extra no-test-edit instruction, so the "
              "stored stricter success flag is not comparable. Elapsed time includes setup and excludes grading; memory was unmeasured.", "",
              "[Run JSON](2026-11-09-flask-budget-diagnostic.json) retains calls, failures, costs, and binary hashes. "
              "The [original public report](2026-11-09-public-sample.md) preserves the earlier results and setup failures.", ""]
    return "\n".join(lines)


def validate_mode(report, diagnostic):
    flags = [row["cohort"] == "flask-budget-diagnostic" for row in report["runs"]]
    if diagnostic and (not flags or not all(flags)):
        raise ValueError("--diagnostic accepts only the separate flask-budget-diagnostic cohort")
    if not diagnostic and any(flags):
        raise ValueError("report the exploratory Flask diagnostic separately with --diagnostic")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directories", nargs="+", type=Path)
    parser.add_argument("--output", type=Path, required=True, help="Output path stem, without suffix")
    parser.add_argument("--diagnostic", action="store_true", help="Separate follow-up; do not add original unavailable slots")
    parser.add_argument("--coq-audit", type=Path, help="Separate typed Coq artifact audit JSON")
    args = parser.parse_args()
    report = summarize(args.directories, include_unavailable=not args.diagnostic)
    try:
        validate_mode(report, args.diagnostic)
    except ValueError as error:
        parser.error(str(error))
    if args.coq_audit:
        report["supplemental_coq_audits"] = json.loads(args.coq_audit.read_text())
        report["supplemental_coq_audit_sha256"] = sha(args.coq_audit)
    args.output.with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
    args.output.with_suffix(".md").write_text(diagnostic_markdown(report) if args.diagnostic else markdown(report))
    print(json.dumps({k: report[k] for k in ["executed_runs", "total_planned_run_slots", "upstream_resolved_runs", "normal_exits", "total_accounted_usd"]}))
