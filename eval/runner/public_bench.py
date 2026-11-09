#!/usr/bin/env python3
"""Small pinned public-benchmark sample using upstream images and verifiers.

This is a local product comparison, not an official leaderboard submission.
No API credential enters a Docker container. Tests are staged only after the
candidate container has stopped; SWE-bench grading uses its official harness in
a fresh image. Terminal-Bench grading uses unchanged upstream test.sh files.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import uuid

from broker import Broker

ROOT = Path(__file__).resolve().parents[2]
LOCK_PATH = ROOT / "eval/public-lock.json"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def command(args, *, timeout=120, cwd=None, output=None, check=True):
    # No ambient API credential or language startup hook reaches docker or the
    # evaluator. The host Broker reads its key separately only in run mode.
    env = {"PATH": os.defpath, "HOME": str(Path.home()), "LANG": "C.UTF-8"}
    if output:
        with Path(output).open("w") as stream:
            completed = subprocess.run(list(map(str, args)), cwd=cwd, env=env,
                                       stdout=stream, stderr=subprocess.STDOUT, timeout=timeout)
    else:
        completed = subprocess.run(list(map(str, args)), cwd=cwd, env=env,
                                   capture_output=True, text=True, timeout=timeout)
    if check and completed.returncode:
        raise RuntimeError(f"{Path(str(args[0])).name} exited {completed.returncode}; see saved output")
    return completed


def docker(*args, **options):
    return command(["docker", *args], **options)


def tasks(lock):
    return lock["terminal_bench"]["tasks"] + lock["swebench"]["tasks"]


def assert_space():
    if shutil.disk_usage(ROOT).free < 4 * 1024 ** 3:
        raise RuntimeError("fewer than 4 GiB free; public evaluation stopped without deleting unrelated data")


def check_assets(lock, tb_repo, dataset, swe_python):
    revision = command(["git", "-C", tb_repo, "rev-parse", "HEAD"]).stdout.strip()
    if revision != lock["terminal_bench"]["commit"]:
        raise RuntimeError("Terminal-Bench checkout differs from lock")
    for task in lock["terminal_bench"]["tasks"]:
        source = tb_repo / task["source_path"]
        for name, digest in task["file_sha256"].items():
            if sha(source / name) != digest:
                raise RuntimeError(f"Terminal-Bench artifact changed: {task['id']}/{name}")
    rows = json.loads(dataset.read_text())
    for task in lock["swebench"]["tasks"]:
        row = next((x for x in rows if x["instance_id"] == task["id"]), None)
        if row is None or row["base_commit"] != task["base_commit"]:
            raise RuntimeError("SWE-bench dataset/base commit differs from lock")
        for name in ["eval_script", "test_patch"]:
            if hashlib.sha256(row[name].encode()).hexdigest() != task[name + "_sha256"]:
                raise RuntimeError(f"SWE-bench {name} differs from lock")
        row["image"] = task["image_digest"]
    version = command([swe_python, "-c", "import swebench;print(swebench.__version__)"]).stdout.strip()
    if version != lock["swebench"]["evaluator_version"]:
        raise RuntimeError("SWE-bench evaluator version differs from lock")
    audit = command([swe_python, "-c",
                     "import hashlib,json,pathlib,swebench,sys;root=pathlib.Path(swebench.__file__).parent;"
                     "print(json.dumps({p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sys.argv[1:]}))",
                     *lock["swebench"]["evaluator_files_sha256"]])
    if json.loads(audit.stdout) != lock["swebench"]["evaluator_files_sha256"]:
        raise RuntimeError("SWE-bench evaluator source differs from pinned revision")
    for task in tasks(lock):
        inspected = json.loads(docker("image", "inspect", task["image_digest"]).stdout)[0]
        if inspected["Id"] != task["image_id"]:
            raise RuntimeError("Docker image differs from lock")
    return rows


def create_container(image, *, workspace, mounts=(), memory="2g"):
    name = "lean-harness-public-" + uuid.uuid4().hex[:12]
    arguments = ["create", "--name", name, "--network", "host", "--cpus", "1", "--memory", memory,
                 "--pids-limit", "256", "--workdir", workspace, "--entrypoint", "/bin/sh"]
    for source, target, writable in mounts:
        spec = f"type=bind,source={Path(source).resolve()},target={target}"
        if not writable:
            spec += ",readonly"
        arguments += ["--mount", spec]
    docker(*arguments, image, "-c", "exec sleep infinity")
    docker("start", name)
    return name


def remove_container(name):
    if name:
        docker("rm", "-f", name, check=False)


def apt_https(container, main_only=False):
    """Opt-in infrastructure repair: same signed Ubuntu repositories, TLS."""
    docker("exec", container, "/bin/sh", "-c",
           "if test -f /etc/apt/sources.list.d/ubuntu.sources; then "
           "sed -i -e 's|http://archive.ubuntu.com|https://archive.ubuntu.com|g' "
           "-e 's|http://security.ubuntu.com|https://security.ubuntu.com|g' "
           "/etc/apt/sources.list.d/ubuntu.sources; fi")
    if main_only:
        # curl's dependencies are in main; avoid downloading the unrelated
        # 19 MB universe index when the upstream mirror is degraded. The Coq
        # compiler is already installed in the immutable official image.
        docker("exec", container, "/bin/sh", "-c",
               "sed -i 's/^Components:.*/Components: main/' /etc/apt/sources.list.d/ubuntu.sources")


def coq_audit(container, directory, workspace):
    """Supplemental kernel-checked statement and assumptions audit, after stop."""
    source = directory / "HarnessProofAudit.v"
    source.write_text("Require Import plus_comm.\n"
        "Definition checked_statement : forall n m : Coq.Init.Datatypes.nat, "
        "@Coq.Init.Logic.eq Coq.Init.Datatypes.nat "
        "(Coq.Init.Nat.add n m) (Coq.Init.Nat.add m n) := plus_comm.plus_comm.\n"
        "Print Assumptions checked_statement.\n")
    docker("cp", source, container + ":/tmp/HarnessProofAudit.v")
    audited = docker("exec", container, "coqc", "-Q", workspace, "", "/tmp/HarnessProofAudit.v", check=False)
    (directory / "assumptions-typed.log").write_text(audited.stdout + audited.stderr)
    # coqc exits nonzero for a type mismatch. Requiring exactly this one output
    # line conservatively rejects any printed axiom list or extra diagnostics.
    return {"version": 2, "type_checked": audited.returncode == 0,
            "closed_assumptions": audited.stdout.strip() == "Closed under the global context",
            "passed": audited.returncode == 0 and audited.stdout.strip() == "Closed under the global context",
            "audit_source_sha256": sha(source)}


def tb_verify(task, image, tb_repo, directory, candidate_workspace=None, use_apt_https=False, apt_main_only=False):
    """Only a new, verifier-only container sees the upstream tests."""
    directory.mkdir(parents=True, exist_ok=True)
    container = None
    try:
        container = create_container(image, workspace=task["workspace"])
        if use_apt_https:
            apt_https(container, apt_main_only)
        if candidate_workspace is not None:
            # Only task artifacts enter a pristine upstream image. Changes to
            # compilers, OpenSSL, Python, curl or package managers in the agent
            # container cannot replace the verifier's trusted implementation.
            docker("exec", container, "/bin/sh", "-c", 'find "$1" -mindepth 1 -maxdepth 1 -exec rm -rf -- {} +',
                   "sh", task["workspace"])
            docker("cp", str(candidate_workspace) + "/.", container + ":" + task["workspace"])
        docker("exec", container, "mkdir", "-p", "/logs/verifier")
        docker("cp", tb_repo / task["source_path"] / "tests", container + ":/tests")
        result = docker("exec", container, "/bin/bash", "/tests/test.sh", timeout=360,
                        output=directory / "verifier.log", check=False)
        docker("cp", container + ":/logs/verifier/.", directory, check=False)
        reward = directory / "reward.txt"
        ctrf = directory / "ctrf.json"
        report = {"official_verifier_exit": result.returncode, "resolved": False, "apt_https": use_apt_https,
                  "apt_main_only": apt_main_only}
        if not reward.is_file() or not ctrf.is_file():
            report["infrastructure_error"] = "upstream verifier did not produce reward and CTRF artifacts"
        else:
            report["official_reward"] = reward.read_text().strip()
            report["resolved"] = report["official_reward"] == "1"
            report["ctrf_sha256"] = sha(ctrf)
        if task["id"] == "prove-plus-comm" and report["resolved"]:
            source = docker("exec", container, "cat", "plus_comm.v").stdout
            statement = bool(re.search(r"Theorem\s+plus_comm\s*:\s*forall\s+n\s+m\s*:\s*nat\s*,\s*n\s*\+\s*m\s*=\s*m\s*\+\s*n\s*\.", source))
            audit = docker("exec", container, "/bin/bash", "-lc",
                           "printf 'Require Import plus_comm.\\nPrint Assumptions plus_comm.plus_comm.\\n' | coqtop -quiet", check=False)
            (directory / "assumptions.log").write_text(audit.stdout + audit.stderr)
            report["additional_proof_integrity"] = statement and "Closed under the global context" in audit.stdout
            report["typed_proof_audit"] = coq_audit(container, directory, task["workspace"])
        return report
    except subprocess.TimeoutExpired:
        return {"resolved": False, "infrastructure_error": "official Terminal-Bench verifier timed out"}
    finally:
        remove_container(container)


def swe_verify(task, prediction, rows, swe_python, directory):
    directory.mkdir(parents=True, exist_ok=True)
    dataset = directory / "dataset.json"
    dataset.write_text(json.dumps([r for r in rows if r["instance_id"] == task["id"]]))
    predictions = directory / "predictions.jsonl"
    predictions.write_text(json.dumps(prediction) + "\n")
    run_id = "public-" + uuid.uuid4().hex[:12]
    verifier_timeout = task.get("verifier_timeout_seconds", 240)
    try:
        result = command([swe_python, "-m", "swebench.harness.run_evaluation", "--dataset_name", dataset,
                          "--predictions_path", predictions, "--max_workers", "1", "--timeout", str(verifier_timeout),
                          "--run_id", run_id], cwd=directory, timeout=verifier_timeout + 90,
                         output=directory / "verifier.log", check=False)
    except subprocess.TimeoutExpired:
        return {"resolved": False, "infrastructure_error": "official SWE-bench verifier timed out", "run_id": run_id}
    report_path = directory / "logs/evaluation" / run_id / "results.json"
    if not report_path.is_file():
        return {"resolved": False, "infrastructure_error": "official SWE-bench report missing",
                "official_verifier_exit": result.returncode, "run_id": run_id}
    report = json.loads(report_path.read_text())
    answer = {"resolved": task["id"] in report.get("resolved_ids", []),
              "official_report": report, "official_verifier_exit": result.returncode,
              "run_id": run_id, "report_sha256": sha(report_path)}
    if task["id"] in report.get("infra_failure_ids", []) or task["id"] in report.get("error_ids", []):
        answer["infrastructure_error"] = report.get("failure_reasons", {}).get(task["id"], "official evaluator execution error")
    return answer


def preflight(lock, rows, args, directory):
    records = []
    for task in tasks(lock):
        if args.tasks and task["id"] not in args.tasks:
            continue
        if task.get("preflight_status") == "ineligible":
            records.append({"task_id": task["id"], "ready": False, "not_run": True,
                            "infrastructure_error": task["preflight_reason"]})
            (directory / "preflight.json").write_text(json.dumps(records, indent=2) + "\n")
            continue
        assert_space()
        target = directory / task["id"]
        target.mkdir()
        if task["benchmark"].startswith("terminal"):
            baseline = tb_verify(task, task["image_digest"], args.tb_repo, target / "baseline",
                                 use_apt_https=args.apt_https, apt_main_only=args.apt_main_only)
            container = create_container(task["image_digest"], workspace=task["workspace"])
            image = None
            try:
                source = args.tb_repo / task["source_path"] / "solution/solve.sh"
                docker("cp", source, container + ":/reference.sh")
                docker("exec", container, "/bin/bash", "/reference.sh", timeout=240,
                       output=target / "reference.log")
                docker("exec", container, "rm", "-f", "/reference.sh")
                docker("stop", "--time", "1", container)
                image = docker("commit", container).stdout.strip()
                reference = tb_verify(task, image, args.tb_repo, target / "reference",
                                      use_apt_https=args.apt_https, apt_main_only=args.apt_main_only)
            except Exception as error:
                reference = {"resolved": False, "infrastructure_error": type(error).__name__ + ": " + str(error)}
            finally:
                remove_container(container)
                if image:
                    docker("image", "rm", image, check=False)
        else:
            row = next(r for r in rows if r["instance_id"] == task["id"])
            neutral = "diff --git a/.evaluation_baseline b/.evaluation_baseline\nnew file mode 100644\n--- /dev/null\n+++ b/.evaluation_baseline\n@@ -0,0 +1 @@\n+baseline\n"
            baseline = swe_verify(task, {"instance_id": task["id"], "model_name_or_path": "baseline", "model_patch": neutral},
                                  rows, args.swe_python, target / "baseline")
            reference = swe_verify(task, {"instance_id": task["id"], "model_name_or_path": "gold", "model_patch": row["patch"]},
                                   rows, args.swe_python, target / "reference")
        records.append({"task_id": task["id"], "baseline": baseline, "reference": reference,
                        "ready": not baseline.get("infrastructure_error") and not baseline["resolved"] and reference["resolved"]})
        (directory / "preflight.json").write_text(json.dumps(records, indent=2) + "\n")
        print(json.dumps(records[-1]), flush=True)
    return records


def run_one(task, engine, repetition, rows, args, directory, broker):
    run_id = f"{task['id']}-{engine}-{repetition}-{uuid.uuid4().hex[:8]}"
    output = directory / run_id
    output.mkdir(mode=0o700)
    sessions = output / "sessions"
    sessions.mkdir()
    endpoint = broker.add_run(run_id, args.max_attempts, args.context_bytes + 24000)
    workspace = task["workspace"]
    if task["benchmark"].startswith("terminal"):
        prompt = (args.tb_repo / task["source_path"] / "instruction.md").read_text()
    else:
        prompt = next(r["problem_statement"] for r in rows if r["instance_id"] == task["id"])
    instructions = (f"You are a coding agent working in {workspace}. Inspect the available files, complete the task, "
                    "run relevant checks, and explain the result. Read before editing and use the returned SHA256 preimage. "
                    "Do not modify existing tests, weaken assertions or change a theorem statement. "
                    "The environment is disposable and command execution is allowed. Work within the task workspace.")
    config = {"model": args.model, "workspace": workspace, "instructions": instructions, "commands": "allow",
              "maxModelAttempts": args.max_attempts, "maxToolCalls": args.max_tools,
              "maxContextBytes": args.context_bytes, "maxOutputTokens": 4096, "maxRetries": 0,
              "operationTimeoutMs": 90000, "maxElapsedMs": args.timeout * 1000,
              "maxToolOutputBytes": 16384, "testEndpoint": endpoint, "compactionEnabled": True}
    (output / "config.json").write_text(json.dumps(config))
    (output / "pi-config.json").write_text(json.dumps({**config, "task": prompt, "track": "product",
        "sessionDir": "/sessions", "toolBinary": "/agent/eval_tools", "schemasPath": "/agent/schemas.json"}))
    node = Path(shutil.which("node")).resolve().parent.parent
    mounts = [(sessions, "/sessions", True), (ROOT / ".lake/build/bin/harness", "/agent/harness", False),
              (ROOT / ".lake/build/bin/eval_tools", "/agent/eval_tools", False),
              (ROOT / "eval/baseline", "/baseline", False), (node, "/opt/node", False),
              (directory / "schemas.json", "/agent/schemas.json", False),
              (output / "config.json", "/agent/config.json", False),
              (output / "pi-config.json", "/agent/pi-config.json", False)]
    record = {"run_id": run_id, "task_id": task["id"], "benchmark": task["benchmark"],
              "engine": engine, "track": "product", "repetition": repetition, "success": False,
              "cohort": args.cohort or task.get("cohort", "original-preselection"),
              "attempt": args.attempt, "apt_https": args.apt_https, "apt_main_only": args.apt_main_only,
              "image_digest": task["image_digest"], "model": args.model}
    container, artifact = None, None
    started = time.monotonic()
    try:
        assert_space()
        container = create_container(task["image_digest"], workspace=workspace, mounts=mounts)
        if args.apt_https:
            apt_https(container, args.apt_main_only)
        # curl is a transport dependency absent from the two official TB bases;
        # retain the exact package list and image ID, while leaving tasks intact.
        docker("exec", container, "/bin/bash", "-lc",
               "command -v /usr/bin/curl >/dev/null || (apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y curl)",
               timeout=180, output=output / "transport-setup.log")
        if task["benchmark"].startswith("SWE"):
            # Discard solution-bearing remote history before either agent runs.
            docker("exec", "-w", workspace, container, "/bin/bash", "-lc",
                   "rm -rf .git && git init -q && git add . && git -c user.name=Evaluation -c user.email=evaluation@localhost commit -qm baseline",
                   timeout=90, output=output / "repository-setup.log")
        path = "/opt/node/bin:/opt/miniconda3/envs/testbed/bin:/usr/local/bin:/usr/bin:/bin"
        invocation = ["exec", "-w", workspace, "-e", "PATH=" + path, container]
        if engine == "lean":
            invocation += ["/agent/harness", "run", "--workspace", workspace, "--config", "/agent/config.json",
                           "--task", prompt, "--session", "/sessions/session", "--json"]
        else:
            invocation += ["/opt/node/bin/node", "/baseline/run.mjs", "/agent/pi-config.json"]
        try:
            result = docker(*invocation, timeout=args.timeout + 15, output=output / "events.log", check=False)
            record["exit_code"] = result.returncode
        except subprocess.TimeoutExpired:
            record["timed_out"] = True
            record["exit_code"] = None
            docker("stop", "--time", "1", container, check=False)
        record["elapsed_seconds"] = round(time.monotonic() - started, 3)
        broker.close_run(run_id)
        if record.get("timed_out"):
            return record
        if engine == "lean":
            inspected = docker("exec", container, "/agent/harness", "inspect", "/sessions/session", check=False)
            (output / "inspection.json").write_text(inspected.stdout)
            if inspected.returncode == 0:
                state = json.loads(inspected.stdout)["state"]
                record.update(model_attempts=state["modelAttempts"], tool_dispatches=state["toolDispatches"],
                              summaries=len(state.get("summaries", [])), unknown_usage=state["unknownUsage"])
        if task["benchmark"].startswith("SWE"):
            docker("exec", "-w", workspace, container, "git", "add", "-N", ".")
            patch = docker("exec", "-w", workspace, container, "git", "diff", "--binary", "HEAD").stdout
            (output / "candidate.patch").write_text(patch)
            changed = docker("exec", "-w", workspace, container, "git", "diff", "--name-only", "HEAD").stdout.splitlines()
            record["test_files_modified"] = [name for name in changed if any(part == "tests" or part.startswith("test_") for part in Path(name).parts)]
            prediction = {"instance_id": task["id"], "model_name_or_path": engine + "-product", "model_patch": patch}
            (output / "predictions.jsonl").write_text(json.dumps(prediction) + "\n")
            docker("stop", "--time", "1", container)
            verdict = swe_verify(task, prediction, rows, args.swe_python, output / "verification")
        else:
            docker("stop", "--time", "1", container)
            docker("cp", container + ":" + workspace + "/.", output / "workspace")
            verdict = tb_verify(task, task["image_digest"], args.tb_repo, output / "verification", output / "workspace",
                                args.apt_https, args.apt_main_only)
        record["checker"] = verdict
        if verdict.get("infrastructure_error"):
            record["infrastructure_error"] = verdict["infrastructure_error"]
        record["success"] = (record["exit_code"] == 0 and verdict["resolved"]
                             and verdict.get("additional_proof_integrity", True)
                             and not record.get("test_files_modified"))
    except Exception as error:
        record["infrastructure_error"] = type(error).__name__ + ": " + str(error)
    finally:
        broker.close_run(run_id)
        remove_container(container)
        if artifact:
            docker("image", "rm", artifact, check=False)
        charged = [r for r in broker.records if r["run_id"] == run_id]
        record.update(provider_attempts=len(charged), accounted_usd=sum(r["charged_usd"] for r in charged),
                      unknown_usage_requests=sum(r["usage"] is None for r in charged))
        (output / "result.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["preflight", "run"])
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--tb-repo", type=Path, default=Path("/tmp/lean-harness-terminal-bench-2-1"))
    parser.add_argument("--swe-python", type=Path, default=Path("/tmp/lean-harness-swebench-venv/bin/python"))
    parser.add_argument("--dataset", type=Path, default=Path("/tmp/lean-harness-public-preflight/swe-dataset.json"))
    parser.add_argument("--tasks", nargs="*")
    parser.add_argument("--engines", nargs="+", choices=["lean", "pi"], default=["lean", "pi"])
    parser.add_argument("--key-file", type=Path)
    parser.add_argument("--budget", type=float, default=35)
    parser.add_argument("--model", default="claude-opus-5-5")
    parser.add_argument("--repetitions", type=int, default=1)
    parser.add_argument("--repetition-start", type=int, default=0)
    parser.add_argument("--attempt", type=int, default=1)
    parser.add_argument("--apt-https", action="store_true", help="Record an opt-in Ubuntu repository transport repair")
    parser.add_argument("--apt-main-only", action="store_true", help="With --apt-https, fetch only main package indexes for curl setup")
    parser.add_argument("--cohort", help="Explicit label for a separately authorized diagnostic cohort")
    parser.add_argument("--max-attempts", type=int, default=12)
    parser.add_argument("--max-tools", type=int, default=24)
    parser.add_argument("--context-bytes", type=int, default=120000)
    parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args()
    if args.apt_main_only and not args.apt_https:
        parser.error("--apt-main-only requires --apt-https")
    directory = args.output.resolve()
    directory.mkdir(mode=0o700, parents=True, exist_ok=False)
    lock = json.loads(LOCK_PATH.read_text())
    shutil.copyfile(LOCK_PATH, directory / "public-lock.json")
    rows = check_assets(lock, args.tb_repo, args.dataset, args.swe_python)
    if args.mode == "preflight":
        results = preflight(lock, rows, args, directory)
        return 0 if all(r["ready"] for r in results) else 1
    if args.key_file is None:
        parser.error("run requires --key-file")
    (directory / "schemas.json").write_bytes(subprocess.check_output([str(ROOT / ".lake/build/bin/eval_tools"), "schemas"]))
    (directory / "plan.json").write_text(json.dumps({"public_lock_sha256": sha(LOCK_PATH),
        "binary_sha256": sha(ROOT / ".lake/build/bin/harness"), "tool_binary_sha256": sha(ROOT / ".lake/build/bin/eval_tools"),
        "pi_lock_sha256": sha(ROOT / "eval/baseline/package-lock.json"), "model": args.model,
        "runner_sha256": sha(__file__), "created_unix": time.time(),
        "budget_usd": args.budget, "repetitions": args.repetitions, "max_attempts": args.max_attempts,
        "repetition_start": args.repetition_start,
        "attempt": args.attempt, "apt_https": args.apt_https, "apt_main_only": args.apt_main_only,
        "cohort": args.cohort,
        "max_tools": args.max_tools, "context_bytes": args.context_bytes, "track": "product",
        "timeout_seconds": args.timeout, "tasks": args.tasks or [t["id"] for t in tasks(lock)], "engines": args.engines}, indent=2))
    results = []
    with Broker(args.key_file.expanduser().read_text().strip(), directory, args.budget, args.model) as broker:
        for repetition in range(args.repetition_start, args.repetition_start + args.repetitions):
            for index, task in enumerate(tasks(lock)):
                if args.tasks and task["id"] not in args.tasks:
                    continue
                engines = args.engines if (index + repetition) % 2 == 0 else list(reversed(args.engines))
                for engine in engines:
                    if task.get("preflight_status") == "ineligible":
                        result = {"task_id": task["id"], "engine": engine, "repetition": repetition,
                                  "success": False, "not_run": True, "provider_attempts": 0, "accounted_usd": 0,
                                  "infrastructure_error": task["preflight_reason"]}
                    else:
                        result = run_one(task, engine, repetition, rows, args, directory, broker)
                    results.append(result)
                    (directory / "results.json").write_text(json.dumps(results, indent=2) + "\n")
                    print(json.dumps({key: result.get(key) for key in ["task_id", "engine", "success", "provider_attempts", "accounted_usd", "infrastructure_error"]}), flush=True)
                    if broker.total >= args.budget - 2:
                        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
