#!/usr/bin/env python3
"""Deterministic, unpaid SWE-bench pilot preparation. Never opens a model API.

The complete dataset, including reference patches, belongs in private taskstate.
Only identifiers, source/image hashes and protocol choices enter selection locks.
Selection is a draft until every offline gate and the funding review has passed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
from docker_endpoint import command_environment

REVISION = "b0dde1093fe417d83b7184254edf8199c1f0dff5"
DATASET_SHA256 = "9535b3885695923512f8e8267646d8566259f6dc1b317033b96dd0f27f10a0e5"
SEED = "lean-harness-linux-pilot-20261109-v1"
DEVELOPMENT_REPOS = ["pytest-dev/pytest", "pylint-dev/pylint", "sphinx-doc/sphinx", "sympy/sympy"]
SEEN = {"pallets__flask-4045", "django__django-11099", "psf__requests-2317"}


def digest(value):
    return hashlib.sha256(value).hexdigest()


def read_dataset(path):
    raw = path.read_bytes()
    if digest(raw) != DATASET_SHA256:
        raise ValueError("dataset bytes differ from the pinned 300-row snapshot")
    rows = json.loads(raw)
    if len(rows) != 300 or len({row["instance_id"] for row in rows}) != 300:
        raise ValueError("expected 300 unique SWE-bench Lite test instances")
    return rows


def rank(scope, identifier):
    return digest(f"{SEED}:{scope}:{identifier}".encode())


def select(rows):
    excluded = [{"id": row["instance_id"], "reason": "previously inspected development task"
                 if row["instance_id"] in SEEN else "Requests external HTTPBIN dependency excluded before outcomes"}
                for row in rows if row["instance_id"] in SEEN or row["repo"] == "psf/requests"]
    excluded_ids = {row["id"] for row in excluded}
    eligible = [row for row in rows if row["instance_id"] not in excluded_ids]
    development = [min((row for row in eligible if row["repo"] == repo),
                       key=lambda row: rank("dev", row["instance_id"])) for repo in DEVELOPMENT_REPOS]
    dev_ids = {row["instance_id"] for row in development}
    grouped = {}
    for row in eligible:
        if row["instance_id"] not in dev_ids:
            grouped.setdefault(row["repo"], []).append(row)
    for group in grouped.values():
        group.sort(key=lambda row: rank("heldout", row["instance_id"]))
    repositories = sorted(grouped, key=lambda repo: rank("repo", repo))
    heldout = [grouped[repo][depth] for depth in range(4) for repo in repositories
               if len(grouped[repo]) > depth][:30]
    describe = lambda row: {"id": row["instance_id"], **{key: row[key] for key in
                            ["repo", "base_commit", "image", "difficulty"]}}
    return {"status": "DRAFT_SELECTION_ONLY_NOT_PREFLIGHTED_OR_FROZEN", "seed": SEED,
            "dataset_revision": REVISION, "dataset_sha256": DATASET_SHA256,
            "algorithm": "Four named development repositories, SHA256 task ranking; SHA256 repository/task order, round-robin depth0..3 for30 heldout IDs; six repeats by independent SHA256 rank",
            "excluded": sorted(excluded, key=lambda row: row["id"]),
            "development": list(map(describe, development)), "heldout": list(map(describe, heldout)),
            "repeats": [row["instance_id"] for row in sorted(heldout, key=lambda row: rank("repeat", row["instance_id"]))[:6]],
            "long_tasks": [],
            "long_task_status": "Unselected: requires substantive issue-only review and fixed independent checks; difficulty labels alone are insufficient"}


def pin_image(row, prior_lock):
    """Pin an already explicitly pulled image. Never pulls or deletes images."""
    inspected = json.loads(subprocess.check_output(["docker", "image", "inspect", row["image"]],
                                                  text=True, env=command_environment()))[0]
    repository = row["image"].rsplit(":", 1)[0]
    digests = [value for value in inspected.get("RepoDigests", []) if value.startswith(repository + "@sha256:")]
    if len(digests) != 1:
        raise ValueError("image lacks a unique digest for the dataset's official repository")
    metadata = {key: value for key, value in prior_lock["swebench"].items() if key != "tasks"}
    metadata.update(dataset_revision=REVISION, dataset_sha256=DATASET_SHA256, tasks=[{
        "id": row["instance_id"], "repo": row["repo"], "benchmark": "SWE-bench Lite",
        "workspace": "/testbed", "base_commit": row["base_commit"], "image_digest": digests[0],
        "image_id": inspected["Id"], "toolchain_roots": ["/opt/miniconda3/envs/testbed"],
        "verifier_timeout_seconds": 900,
        **{key + "_sha256": digest(row[key].encode()) for key in ["eval_script", "test_patch", "problem_statement"]}}])
    return {"status": "DRAFT_OFFLINE_PREFLIGHT_ONLY", "selection_seed": SEED,
            "swebench": metadata, "terminal_bench": {"tasks": []}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["select", "pin-image"])
    parser.add_argument("--dataset", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--task")
    parser.add_argument("--evaluator-lock", type=Path, default=Path(__file__).resolve().parents[1] / "public-lock.json")
    args = parser.parse_args()
    rows = read_dataset(args.dataset)
    if args.mode == "select":
        value = select(rows)
    else:
        if not args.task:
            parser.error("pin-image requires --task")
        row = next((row for row in rows if row["instance_id"] == args.task), None)
        if row is None:
            parser.error("task is absent from the pinned dataset")
        value = pin_image(row, json.loads(args.evaluator_lock.read_text()))
    with args.output.open("x") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")
    args.output.chmod(0o600)


if __name__ == "__main__":
    main()
