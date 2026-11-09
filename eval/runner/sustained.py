#!/usr/bin/env python3
"""Four explicit sustained-use modes using the public runner's existing boundary.

Self-authored repository feature tasks use their own frozen checker, never a
SWE-bench score. Reference patches are used only by offline preflight. A frozen
manifest must declare every mode, task, checker file and expected result shape.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path
import shutil
from types import SimpleNamespace
import subprocess

from audit_continuation import AuditError, audit_run
from broker import Broker, output_ceiling
from request_evidence import REQUEST_EVIDENCE_VERSION
from paths import (add_harness_root_argument, eval_tools_binary, evaluation_provenance,
                   harness_binary, harness_root, node_root, product_provenance, require_fresh_harness)
import public_bench as public
from workspace_snapshot import read_regular_file


def checked_file(record):
    path = Path(record["path"]).expanduser().resolve()
    if not path.is_file() or public.sha(path) != record["sha256"]:
        raise ValueError("frozen sustained artifact missing or changed: " + str(path))
    return path


def validate_manifest(manifest):
    if manifest.get("schema_version") != 1:
        raise ValueError("unsupported sustained manifest schema")
    tasks, modes = manifest["tasks"], manifest["modes"]
    if len({task["id"] for task in tasks}) != len(tasks) or len({mode["id"] for mode in modes}) != len(modes):
        raise ValueError("duplicate task or mode identity")
    for task in tasks:
        if hashlib.sha256(task["task_text"].encode()).hexdigest() != task["task_sha256"]:
            raise ValueError("sustained task wording changed")
        image = task["image_digest"].split("@sha256:")
        if len(image) != 2 or not image[0] or len(image[1]) != 64 or any(c not in "0123456789abcdef" for c in image[1]):
            raise ValueError("sustained image must be digest pinned")
        files = task["checker"]["files"]
        destinations = [file["name"] for file in files]
        if len(set(destinations)) != len(destinations) or any(Path(name).name != name or name in {"", ".", ".."} for name in destinations):
            raise ValueError("checker mounts must have unique simple filenames")
        for file in files:
            checked_file(file)
        checked_file(task["reference_patch"])
        if not task["checker"].get("expected_counts"):
            raise ValueError("checker must declare an expected result shape")
    for mode in modes:
        if mode["engine"] not in {"lean", "pi"}:
            raise ValueError("unsupported sustained engine")
        for field in ["max_attempts", "max_tools", "context_bytes", "timeout"]:
            if type(mode[field]) is not int or mode[field] <= 0:
                raise ValueError("mode limits must be positive integers")
        if mode.get("yield_after", 0) not in {0, 12} or (mode["engine"] == "pi" and mode.get("yield_after", 0)):
            raise ValueError("restart mode supports Lean with the frozen12-completion yield interval")
        allowed = {"compactAtPercent", "compactionKeepMessages", "maxSummaryBytes", "maxOutputTokens", "maxToolOutputBytes", "maxResponseRepairs"}
        config = mode.get("config", {})
        if set(config) - allowed or any(type(value) is not int or value < 0 for value in config.values()):
            raise ValueError("unsupported mode configuration")
        output_ceiling(config.get("maxOutputTokens", 4096))
        public.validate_pi_settings(mode.get("pi", {}), mode["engine"])
    return manifest


def verify_feature(task, prediction, directory):
    """Apply only the candidate patch in a fresh, unprivileged verifier image."""
    directory.mkdir(parents=True, exist_ok=True)
    patch = directory / "candidate.patch"
    patch.write_text(prediction["model_patch"])
    spec = task["checker"]
    mounts = [(checked_file(file), "/checker/" + file["name"], False) for file in spec["files"]]
    container = None
    report = {"passed": False, "resolved": False, "benchmark": "self-authored sustained repository feature"}
    try:
        public.assert_space()
        container = public.create_container(task["image_digest"], workspace=task["workspace"], mounts=mounts,
                                           memory=spec.get("memory", "2g"), network="none")
        if patch.stat().st_size:
            public.docker("cp", patch, container + ":/tmp/candidate.patch")
            applied = public.docker("exec", "-w", task["workspace"], container, "git", "-c", "core.hooksPath=/dev/null",
                                    "-c", "core.fsmonitor=false", "apply", "/tmp/candidate.patch", check=False)
            (directory / "patch-application.log").write_text(applied.stdout + applied.stderr)
            if applied.returncode:
                return {**report, "patch_application_failed": True}
        result = public.docker("exec", "-w", task["workspace"], container, *spec["command"],
                               timeout=spec.get("timeout_seconds", 120), output=directory / "checker.log", check=False)
        report["checker_exit_code"] = result.returncode
        if spec.get("result_file"):
            raw = read_regular_file(container, spec["result_file"], 2_000_000).decode("utf-8")
            (directory / "checker-result.json").write_text(raw)
        else:
            raw = (directory / "checker.log").read_text()
        if spec.get("format", "json") == "unittest":
            matches = re.findall(r"^Ran (\d+) tests? in [\d.]+s$", raw, flags=re.MULTILINE)
            checked = {"tests_run": int(matches[-1]) if matches else None,
                       "passed": result.returncode == 0 and bool(re.search(r"\nOK(?: \([^\n]*\))?\s*$", raw))}
        else:
            try:
                checked = json.loads(raw)
            except ValueError:
                return {**report, "checker_report_invalid": True,
                        "expected_baseline_failure": bool(spec.get("baseline_failure_contains")) and
                            spec["baseline_failure_contains"] in raw and result.returncode != 0}
        report["details"] = checked
        report["result_shape_matches"] = all(checked.get(key) == value for key, value in spec["expected_counts"].items())
        report["passed"] = result.returncode == 0 and checked.get("passed") is True and report["result_shape_matches"]
        original = task.get("original_tests")
        if original:
            regression = public.docker("exec", "-w", task["workspace"], container, *original["command"],
                timeout=original.get("timeout_seconds", 180), output=directory / "original-tests.log", check=False)
            report["original_tests_exit_code"] = regression.returncode
            report["passed"] = report["passed"] and regression.returncode == original.get("expected_exit_code", 0)
        report["resolved"] = report["passed"]
        return report
    except subprocess.TimeoutExpired:
        return {**report, "checker_timeout": True}
    finally:
        public.remove_container(container)


def audit_restart(directory, plan):
    # run_one settles this run and saves the broker ledger before returning.
    # The auditor needs both charges and the frozen prices that produced them.
    ledger = json.loads((directory.parent / "broker.json").read_text())
    return audit_run(directory, ledger, plan)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    add_harness_root_argument(parser)
    parser.add_argument("operation", choices=["preflight", "run"])
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--tasks", nargs="*")
    parser.add_argument("--modes", nargs="*")
    parser.add_argument("--prepared-bwrap", type=Path, required=True)
    parser.add_argument("--bwrap-sha256", required=True)
    parser.add_argument("--key-file", type=Path)
    parser.add_argument("--campaign-dir", type=Path)
    parser.add_argument("--allocation", default="long")
    parser.add_argument("--budget", type=float, default=28)
    parser.add_argument("--retain-responses", action="store_true", help="retain bounded private provider-body diagnostics")
    parser.add_argument("--task-context-version", type=int, choices=[1, 2, 3, 4], default=1,
                        help="Frozen Lean context: legacy1, budget-notice2, command-time-limit3, application-context4")
    options = parser.parse_args()
    manifest = validate_manifest(json.loads(options.manifest.read_text()))
    if options.operation == "run" and manifest.get("status") != "FROZEN_SUSTAINED":
        parser.error("paid execution requires an offline-reviewed frozen sustained manifest")
    public.prepared_sandbox(options)
    selected = [task for task in manifest["tasks"] if not options.tasks or task["id"] in options.tasks]
    modes = [mode for mode in manifest["modes"] if not options.modes or mode["id"] in options.modes]
    if (options.tasks and set(options.tasks) - {task["id"] for task in selected}) or (options.modes and set(options.modes) - {mode["id"] for mode in modes}):
        parser.error("selected task or mode is absent from the frozen manifest")
    output = options.output.resolve()
    output.mkdir(parents=True, mode=0o700, exist_ok=False)
    public.ACTIVE_OWNER = public.Owner(output)
    shutil.copyfile(options.manifest, output / "manifest.json")
    for task in selected:
        public.docker("image", "inspect", task["image_digest"])
    if options.operation == "preflight":
        results = []
        for task in selected:
            baseline = verify_feature(task, {"model_patch": ""}, output / task["id"] / "baseline")
            reference = verify_feature(task, {"model_patch": checked_file(task["reference_patch"]).read_text()},
                                       output / task["id"] / "reference")
            results.append({"task_id": task["id"], "baseline": baseline, "reference": reference,
                            "passed": not baseline["passed"] and reference["passed"] and
                                (baseline.get("result_shape_matches") is True or baseline.get("expected_baseline_failure") is True)})
            (output / "preflight.json").write_text(json.dumps(results, indent=2) + "\n")
        return 0 if all(row["passed"] for row in results) else 1
    if options.key_file is None or options.campaign_dir is None:
        parser.error("paid execution requires the shared campaign ledger and a private key file")
    root = harness_root(options.harness_root)
    require_fresh_harness(root)
    proxy = eval_tools_binary(root)
    node_root()
    (output / "schemas.json").write_bytes(subprocess.check_output([str(proxy), "schemas"]))
    plan = {"schema_version": 1, "benchmark": "self-authored sustained repository features", "modes": modes,
            "tasks": [task["id"] for task in selected], "all_declared_tasks": [task["id"] for task in manifest["tasks"]],
            "manifest_sha256": public.sha(options.manifest), "binary_sha256": public.sha(harness_binary(root)),
            "task_context_version": options.task_context_version,
            "request_evidence_version": REQUEST_EVIDENCE_VERSION,
            "tool_binary_sha256": public.sha(proxy), "tool_schemas_sha256": public.sha(output / "schemas.json"),
            "prepared_bwrap_sha256": options.bwrap_sha256,
            "budget_usd": options.budget, "retain_responses": options.retain_responses, "model": manifest.get("model", "claude-opus-5-5"),
            "shared_user_constraints": public.TASK_CONSTRAINTS,
            "qualification_version": public.QUALIFICATION_VERSION,
            "qualification_rule": public.QUALIFICATION_RULE,
            **product_provenance(root), **evaluation_provenance()}
    plan.update(snapshot_limits=public.SNAPSHOT_LIMITS, snapshot_exclusions=public.SNAPSHOT_EXCLUSIONS,
                session_mirror_limits=public.SESSION_LIMITS,
                session_audit_provenance="regular-only host audit mirrors; original journal remains in prepared container through restarts")
    (output / "plan.json").write_text(json.dumps(plan, indent=2) + "\n")
    results = []
    with Broker(options.key_file.expanduser().read_text().strip(), output, options.budget, plan["model"],
                campaign=options.campaign_dir, allocation=options.allocation, retain_responses=options.retain_responses) as broker:
        scheduled = [(task, mode) for task in selected for mode in modes]
        for slot, (task, mode) in enumerate(scheduled):
            args = SimpleNamespace(harness_root=root, prepared_bwrap=options.prepared_bwrap,
                bwrap_sha256=options.bwrap_sha256, model=plan["model"], max_attempts=mode["max_attempts"],
                max_tools=mode["max_tools"], context_bytes=mode["context_bytes"], timeout=mode["timeout"],
                config_overrides=mode.get("config", {}), yield_after=mode.get("yield_after", 0), max_invocations=128,
                pi_settings=mode.get("pi", {}),
                mode_id=mode["id"], cohort=manifest.get("cohort", "sustained"), attempt=1,
                task_context_version=options.task_context_version,
                apt_https=True, apt_main_only=False)
            prepared_task = {**task, "repository_task": True, "benchmark": "self-authored sustained repository feature"}
            record = public.run_one(prepared_task, mode["engine"], 0, [], args, output, broker,
                                    task_text=task["task_text"], verify_patch=verify_feature)
            if mode.get("yield_after"):
                try:
                    record["continuation_audit"] = audit_restart(output / record["run_id"], plan)
                except (AuditError, KeyError, OSError, TypeError, ValueError) as error:
                    record["continuation_audit"] = {"status": "failed", "reason": str(error)}
                record["sustained_gate_passed"] = record["continuation_audit"].get("status") == "passed"
                record["automated_qualification_checks"] = public.automated_checks(record)
                (output / record["run_id"] / "result.json").write_text(json.dumps(record, indent=2) + "\n")
            results.append(record)
            stop_reason = public.cohort_stop_reason(record)
            if stop_reason:
                results.extend(public.unrun_slot(next_task["id"], next_mode["engine"], 0, stop_reason,
                                                mode=next_mode["id"])
                               for next_task, next_mode in scheduled[slot + 1:])
            (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
            print(json.dumps({key: record.get(key) for key in ["task_id", "mode", "artifact_pass", "normal_finish", "qualification_status", "sustained_gate_passed", "accounted_usd"]}), flush=True)
            if stop_reason:
                return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
