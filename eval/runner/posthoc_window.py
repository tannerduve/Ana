#!/usr/bin/env python3
"""Isolated post hoc numeric probe; never updates frozen benchmark metrics.

Only a byte-for-byte copy of window.js is exposed to each candidate process.
Expected answers, cases, references, journals, and the original workspaces stay
outside its mount namespace. This supplements the frozen checker; it does not
change that checker or turn this one example into a general correctness result.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import stat
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
TASK = "dev08-js-window"
MAX_VALUE = sys.float_info.max
EXPECTED = [
    {"kind": "finite", "value": "-1.7976931348623157e+308"},
    {"kind": "finite", "value": "1.7976931348623157e+308"},
]
OUTPUT_LIMIT = 65536

# Inputs enter over stdin. The expected answer is compared only in the parent.
# Tagged values preserve Infinity/NaN, which JSON.stringify normally makes null.
WORKER = r"""
const fs = require('node:fs');
const input = JSON.parse(fs.readFileSync(0, 'utf8'));
const before = JSON.stringify(input.values);
function encode(value) {
  if (typeof value !== 'number') return {kind:'non-number',type:typeof value};
  if (Number.isNaN(value)) return {kind:'non-finite',value:'NaN'};
  if (value === Infinity) return {kind:'non-finite',value:'Infinity'};
  if (value === -Infinity) return {kind:'non-finite',value:'-Infinity'};
  return {kind:'finite',value:Object.is(value,-0)?'-0':String(value)};
}
let observation;
try {
  const value = require('/candidate/window.js').windowSums(input.values,input.width);
  observation = Array.isArray(value) ? {value:value.map(encode)} : {error:'non-array result'};
} catch (error) {
  observation = {error:typeof error?.name === 'string' ? error.name : 'unknown exception'};
}
observation.input_preserved = before === JSON.stringify(input.values);
process.stdout.write(JSON.stringify(observation)+'\n');
"""


class AuditError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def source_bytes(path):
    require(stat.S_ISREG(path.lstat().st_mode), f"not a regular source file: {path.name}")
    require(path.stat().st_size <= 1_000_000, "source exceeds audit size limit")
    return path.read_bytes()


def environment():
    return {"PATH": "/usr/bin:/bin", "HOME": "/nonexistent", "LANG": "C.UTF-8"}


def limit_output():
    # Files, rather than unbounded captured pipes, retain candidate output. This
    # limit is inherited by candidate children and never changes the host limit.
    resource.setrlimit(resource.RLIMIT_FSIZE, (OUTPUT_LIMIT, OUTPUT_LIMIT))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def isolated_command(directory, node):
    bwrap = shutil.which("bwrap")
    require(bwrap is not None, "bubblewrap unavailable; refusing unisolated execution")
    command = [bwrap, "--unshare-all", "--die-with-parent", "--new-session",
               "--clearenv"]
    for name, value in environment().items():
        command += ["--setenv", name, value]
    # No host /tmp, /home, checker, corpus, reference tree, or workspace mount.
    for path in ["/usr", "/lib", "/lib64"]:
        if Path(path).exists():
            command += ["--ro-bind", path, path]
    command += ["--symlink", "/usr/bin", "/bin", "--dev", "/dev",
                "--proc", "/proc", "--tmpfs", "/tmp",
                "--ro-bind", node, "/runtime/node",
                "--ro-bind", str(directory), "/candidate", "--chdir", "/candidate",
                "/runtime/node", "--no-addons", "-e", WORKER]
    return command


def run_source(source, *, node=None):
    node = node or shutil.which("node")
    require(node is not None, "node unavailable")
    node = str(Path(node).resolve())
    require(Path(node).is_file(), "node executable unavailable")
    with tempfile.TemporaryDirectory(prefix="harness-window-posthoc-") as temporary:
        directory = Path(temporary)
        (directory / "window.js").write_bytes(source)
        with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
            try:
                result = subprocess.run(
                    isolated_command(directory, node), input=json.dumps(
                        {"values": [-MAX_VALUE, MAX_VALUE], "width": 1}).encode(),
                    stdout=stdout, stderr=stderr, env=environment(), timeout=10,
                    preexec_fn=limit_output)
            except subprocess.TimeoutExpired:
                return {"status": "execution_error", "reason": "timeout", "passed": False}
            stdout.seek(0)
            output = stdout.read(OUTPUT_LIMIT + 1)
            stderr.seek(0)
            errors = stderr.read(OUTPUT_LIMIT + 1)
        require((directory / "window.js").read_bytes() == source, "source copy changed")
    if len(output) >= OUTPUT_LIMIT or len(errors) >= OUTPUT_LIMIT:
        return {"status": "execution_error", "reason": "output limit", "passed": False}
    if result.returncode != 0:
        return {"status": "execution_error", "reason": "nonzero exit",
                "exit_code": result.returncode, "passed": False,
                "stderr_sha256": digest(errors)}
    try:
        actual = json.loads(output)
    except (ValueError, UnicodeError):
        return {"status": "execution_error", "reason": "invalid observation", "passed": False}
    if not isinstance(actual, dict) or type(actual.get("input_preserved")) is not bool:
        return {"status": "execution_error", "reason": "invalid observation shape", "passed": False}
    return {"status": "observed", "actual": actual,
            "passed": actual == {"value": EXPECTED, "input_preserved": True}}


def audit(directory):
    directory = Path(directory).resolve()
    corpus = ROOT / "eval/corpus"
    manifest_data = (corpus / "manifest.json").read_bytes()
    manifest = json.loads(manifest_data)
    plan_data = (directory / "plan.json").read_bytes()
    plan = json.loads(plan_data)
    require(plan["manifest_sha256"] == digest(manifest_data), "frozen manifest differs")
    require(TASK in plan["tasks"], "task absent from evaluation plan")
    task = next(task for task in manifest["tasks"] if task["id"] == TASK)
    readme = (corpus / task["fixture"] / "README.md").read_bytes()
    require(digest(readme) == task["artifact_sha256"]["README.md"], "task README differs")
    # Do not inspect hidden cases; retain their fixed hash and check immutability.
    cases_before = (corpus / task["cases"]).read_bytes()
    require(digest(cases_before) == task["case_sha256"], "frozen cases differ")
    reference_path = corpus / task["reference"] / "window.js"
    reference_source = source_bytes(reference_path)
    require(digest(reference_source) == task["reference_sha256"]["window.js"],
            "frozen reference differs")
    node = shutil.which("node")
    require(node is not None, "node unavailable")
    node = str(Path(node).resolve())
    version = subprocess.run([node, "--version"], env=environment(), capture_output=True,
                             text=True, check=True, timeout=5).stdout.strip()
    reference = {"source_sha256": digest(reference_source),
                 **run_source(reference_source, node=node)}
    records, seen = [], set()
    for run in sorted(directory.glob(TASK + "-*")):
        result_path = run / "result.json"
        if not result_path.is_file():
            continue
        require(not run.is_symlink(), "run directory is a symlink")
        result_data = result_path.read_bytes()
        result = json.loads(result_data)
        require(result["run_id"] == run.name and result["task_id"] == TASK,
                "run identity differs")
        key = (result["track"], result["engine"], result["repetition"])
        require(key[0] in plan["tracks"] and key[1] in plan["engines"] and
                type(key[2]) is int and 0 <= key[2] < plan["repetitions"],
                "run is outside frozen plan")
        require(key not in seen, "duplicate planned run")
        seen.add(key)
        path = run / "workspace/window.js"
        source = source_bytes(path)
        sha = digest(source)
        require(sha == result["checker"]["candidate_sha256"]["window.js"],
                f"candidate differs from checked artifact: {run.name}")
        observation = run_source(source, node=node)
        require(source_bytes(path) == source and result_path.read_bytes() == result_data,
                "original candidate or result changed during probe")
        records.append({"run_id": run.name, "track": key[0], "engine": key[1],
                        "repetition": key[2], "source_sha256": sha,
                        "frozen_result_sha256": digest(result_data),
                        "frozen_checker_passed": result["checker_passed"],
                        "frozen_success": result["success"], **observation})
    require((corpus / "manifest.json").read_bytes() == manifest_data and
            (corpus / task["cases"]).read_bytes() == cases_before and
            source_bytes(reference_path) == reference_source and
            (directory / "plan.json").read_bytes() == plan_data,
            "frozen evaluation input changed during audit")
    expected_count = len(plan["tracks"]) * len(plan["engines"]) * plan["repetitions"]
    return {
        "schema_version": 1,
        "generated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "task_id": TASK,
        "classification": "post hoc diagnostic outside frozen benchmark metrics",
        "rationale": "Both inputs are finite numbers and width 1 is a positive integer. "
                     "Each one-element window must sum to its sole element; no sum overflows. "
                     "This checks an ordinary functional edge case, not an integrity violation.",
        "case": {"values": ["-Number.MAX_VALUE", "Number.MAX_VALUE"], "width": 1,
                 "expected": {"value": EXPECTED, "input_preserved": True}},
        "frozen_metrics_modified": False,
        "manifest_sha256": digest(manifest_data), "plan_sha256": digest(plan_data),
        "readme_sha256": digest(readme), "cases_sha256": digest(cases_before),
        "auditor_sha256": digest(Path(__file__).read_bytes()),
        "worker_sha256": digest(WORKER.encode()),
        "runtime": {"node": node, "version": version,
                    "binary_sha256": digest(Path(node).read_bytes())},
        "isolation": {"mounts": "read-only system runtime and source-only /candidate copy",
                      "network": "new unshared network namespace", "proc": "new PID namespace",
                      "environment": "explicit PATH/HOME/LANG only", "timeout_seconds": 10,
                      "stdout_stderr_cap_bytes_each": OUTPUT_LIMIT},
        "expected_candidate_count": expected_count,
        "completed_candidate_count": len(records), "cohort_complete": len(records) == expected_count,
        "reference": reference, "candidates": records,
        "summary": {"passed": sum(record["passed"] for record in records),
                    "failed": sum(record["status"] == "observed" and not record["passed"]
                                  for record in records),
                    "execution_errors": sum(record["status"] != "observed" for record in records)},
        "limitations": ["The case was selected after inspecting completed solutions.",
                        "Frozen benchmark scores and denominators are unchanged.",
                        "Passing this one case does not establish general numeric correctness."]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    try:
        report = audit(args.directory)
        encoded = json.dumps(report, indent=2, allow_nan=False) + "\n"
        if args.output:
            args.output.write_text(encoded)
        else:
            print(encoded, end="")
        print(json.dumps({"completed": report["completed_candidate_count"],
                          "cohort_complete": report["cohort_complete"],
                          "reference_passed": report["reference"]["passed"],
                          **report["summary"]}), file=sys.stderr)
        return int(report["reference"]["status"] != "observed" or
                   report["summary"]["execution_errors"] != 0 or
                   (args.require_complete and not report["cohort_complete"]))
    except (AuditError, OSError, ValueError, KeyError, StopIteration, subprocess.SubprocessError) as error:
        print(json.dumps({"audit_error": str(error)}), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
