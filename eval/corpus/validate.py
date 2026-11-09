#!/usr/bin/env python3
"""Validate fixtures and references without using a model or changing the corpus."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

import check


def prepare_compilers():
    """Resolve host toolchain shims before the checker removes HOME and PATH."""
    repository = check.ROOT.parents[1]
    if not os.environ.get("LEAN_BIN"):
        prefix = subprocess.check_output(
            ["lean", "--print-prefix"], cwd=repository, text=True).strip()
        os.environ["LEAN_BIN"] = str(Path(prefix) / "bin/lean")
    if not os.environ.get("RUSTC_BIN"):
        os.environ["RUSTC_BIN"] = subprocess.check_output(
            ["rustup", "which", "rustc"], cwd=repository, text=True).strip()


def validate():
    prepare_compilers()
    manifest = json.loads((check.ROOT / "manifest.json").read_text())
    rows = []
    for task in manifest["tasks"]:
        fixture = check.ROOT / task["fixture"]
        reference = check.ROOT / task["reference"]
        for name, digest in task["artifact_sha256"].items():
            if hashlib.sha256((fixture / name).read_bytes()).hexdigest() != digest:
                raise RuntimeError(f"fixture artifact changed: {task['id']}/{name}")
        for name, digest in task["reference_sha256"].items():
            if hashlib.sha256((reference / name).read_bytes()).hexdigest() != digest:
                raise RuntimeError(f"reference artifact changed: {task['id']}/{name}")
        started = time.monotonic()
        baseline = check.evaluate(task["id"], fixture)
        with tempfile.TemporaryDirectory(prefix="corpus-reference-") as scratch:
            workspace = Path(scratch) / "workspace"
            shutil.copytree(fixture, workspace)
            for name in task["editable"]:
                shutil.copyfile(reference / name, workspace / name)
            solved = check.evaluate(task["id"], workspace)
        row = {"task_id": task["id"], "split": task["split"],
               "baseline_failed": not baseline["passed"], "reference_passed": solved["passed"],
               "case_count": solved["case_count"], "seconds": round(time.monotonic() - started, 3),
               "reference_failures": solved["failures"]}
        rows.append(row)
        print(json.dumps(row), flush=True)
    return {"schema_version": 1, "kind": "fixture validation; no agent performance measurement",
            "manifest_sha256": hashlib.sha256((check.ROOT / "manifest.json").read_bytes()).hexdigest(),
            "passed": all(row["baseline_failed"] and row["reference_passed"] for row in rows), "tasks": rows}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = validate()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"passed": result["passed"], "tasks": len(result["tasks"])}))
    raise SystemExit(0 if result["passed"] else 1)
