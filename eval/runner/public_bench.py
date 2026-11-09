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
import stat
import subprocess
import sys
import time
import uuid

from broker import Broker, output_ceiling
from request_evidence import REQUEST_EVIDENCE_VERSION, audit_initial_task
from resource_owner import Owner
from patch_review import VERSION as QUALIFICATION_VERSION, TASK_CONSTRAINTS, QUALIFICATION_RULE, automated_checks
from session_audit import AuditError, completed_session
from container_memory import ContainerMemory
from workspace_snapshot import (capture_baseline, capture_candidate_after_stop, LIMITS as SNAPSHOT_LIMITS,
                                EXCLUSION_POLICY as SNAPSHOT_EXCLUSIONS, read_regular_file,
                                mirror_session_after_stop, SESSION_LIMITS)
from paths import (EVAL_ROOT, add_harness_root_argument, eval_tools_binary, evaluation_provenance,
                   harness_binary, harness_root, node_root, node_identity, validate_node_preflight, product_provenance, require_fresh_harness)
from docker_endpoint import command_environment, docker_host

ROOT = EVAL_ROOT
ACTIVE_OWNER = None
LOCK_PATH = ROOT / "public-lock.json"
NESTED_SANDBOX_FLAGS = ["--security-opt", "seccomp=unconfined",
                        "--security-opt", "apparmor=unconfined",
                        "--security-opt", "systempaths=unconfined", "--cap-add", "SYS_ADMIN"]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def command(args, *, timeout=120, cwd=None, output=None, check=True):
    # No ambient API credential or language startup hook reaches docker or the
    # evaluator. The host Broker reads its key separately only in run mode.
    env = command_environment()
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
    return lock.get("terminal_bench", {}).get("tasks", []) + lock.get("swebench", {}).get("tasks", [])


def assert_space():
    if shutil.disk_usage(ROOT).free < 4 * 1024 ** 3:
        raise RuntimeError("fewer than 4 GiB free; public evaluation stopped without deleting unrelated data")


def check_assets(lock, tb_repo, dataset, swe_python, selected=None):
    admitted = [task for task in tasks(lock) if not selected or task["id"] in selected]
    if selected and set(selected) - {task["id"] for task in admitted}:
        raise RuntimeError("selected task is absent from the lock")
    terminal = [task for task in admitted if task["benchmark"].startswith("terminal")]
    swe = [task for task in admitted if task["benchmark"].startswith("SWE")]
    if terminal:
        revision = command(["git", "-C", tb_repo, "rev-parse", "HEAD"]).stdout.strip()
        if revision != lock["terminal_bench"]["commit"]:
            raise RuntimeError("Terminal-Bench checkout differs from lock")
    for task in terminal:
        source = tb_repo / task["source_path"]
        for name, digest in task["file_sha256"].items():
            if sha(source / name) != digest:
                raise RuntimeError(f"Terminal-Bench artifact changed: {task['id']}/{name}")
    rows = json.loads(dataset.read_text()) if swe else []
    if swe and lock["swebench"].get("dataset_sha256") and sha(dataset) != lock["swebench"]["dataset_sha256"]:
        raise RuntimeError("SWE-bench dataset bytes differ from lock")
    for task in swe:
        row = next((x for x in rows if x["instance_id"] == task["id"]), None)
        if row is None or row["base_commit"] != task["base_commit"]:
            raise RuntimeError("SWE-bench dataset/base commit differs from lock")
        for name in ["eval_script", "test_patch"]:
            if hashlib.sha256(row[name].encode()).hexdigest() != task[name + "_sha256"]:
                raise RuntimeError(f"SWE-bench {name} differs from lock")
        row["image"] = task["image_digest"]
    if swe:
        version = command([swe_python, "-c", "import swebench;print(swebench.__version__)"]).stdout.strip()
        if version != lock["swebench"]["evaluator_version"]:
            raise RuntimeError("SWE-bench evaluator version differs from lock")
        audit = command([swe_python, "-c",
                     "import hashlib,json,pathlib,swebench,sys;root=pathlib.Path(swebench.__file__).parent;"
                     "print(json.dumps({p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sys.argv[1:]}))",
                     *lock["swebench"]["evaluator_files_sha256"]])
        if json.loads(audit.stdout) != lock["swebench"]["evaluator_files_sha256"]:
            raise RuntimeError("SWE-bench evaluator source differs from pinned revision")
    for task in admitted:
        inspected = json.loads(docker("image", "inspect", task["image_digest"]).stdout)[0]
        if inspected["Id"] != task["image_id"]:
            raise RuntimeError("Docker image differs from lock")
    return rows


def create_container(image, *, workspace, mounts=(), memory="2g", nested_sandbox=False, network="host"):
    name = "lean-harness-public-" + uuid.uuid4().hex[:12]
    arguments = ["create", "--name", name, "--network", network, "--cpus", "1", "--memory", memory,
                 "--pids-limit", "256", "--workdir", workspace, "--entrypoint", "/bin/sh"]
    if nested_sandbox:
        # The outer container hosts a trusted runner. These flags permit its
        # nested namespaces; the production bwrap profile is the tool boundary.
        arguments += NESTED_SANDBOX_FLAGS
    for source, target, writable in mounts:
        spec = f"type=bind,source={Path(source).resolve()},target={target}"
        if not writable:
            spec += ",readonly"
        arguments += ["--mount", spec]
    if ACTIVE_OWNER is not None:
        arguments += ['--label', ACTIVE_OWNER.intent(name, str(image))]
    try:
        created = docker(*arguments, image, "-c", "exec sleep infinity")
        if ACTIVE_OWNER is not None:
            ACTIVE_OWNER.created(name, created.stdout.strip())
        docker("start", name)
    except BaseException:
        if ACTIVE_OWNER is not None:
            ACTIVE_OWNER.uncertain = True
            ACTIVE_OWNER.cleanup()
        raise
    return name


def remove_container(name):
    if name:
        docker("rm", "-f", name)


def prepared_sandbox(args):
    if args.prepared_bwrap is None:
        if args.bwrap_sha256:
            raise RuntimeError("--bwrap-sha256 requires --prepared-bwrap")
        return None
    path = args.prepared_bwrap.resolve()
    if not path.is_file() or not os.access(path, os.X_OK) or sha(path) != args.bwrap_sha256:
        raise RuntimeError("prepared bubblewrap executable is missing or differs from --bwrap-sha256")
    if path.stat().st_mode & (stat.S_ISUID | stat.S_ISGID):
        raise RuntimeError("prepared bubblewrap must be a non-setuid/non-setgid executable")
    return {"profile": "bubblewrap", "binary_sha256": sha(path),
            "outer_docker_flags": NESTED_SANDBOX_FLAGS,
            "outer_boundary": "trusted runner; no outer-container security claim",
            "pi_product_profile": "ordinary Docker; native tools do not use the Lean sandbox"}


def toolchain_roots(task):
    return task.get("toolchain_roots", ["/opt/miniconda3/envs/testbed"] if is_repository_task(task) else [])


def is_repository_task(task):
    return task["benchmark"].startswith("SWE") or task.get("repository_task") is True


def production_smoke(task, container, args, directory):
    """Run the real Lean CLI with scripted observations; no provider is contacted.

    The command writes through /workspace and the file tool reads through the
    canonical root. The read, capability drop and interpreter checks must all
    pass before a live broker capability is registered.
    """
    directory.mkdir(parents=True, exist_ok=True)
    workspace = task["workspace"]
    marker = ".harness-production-profile-probe-" + uuid.uuid4().hex
    probe = ("import os,pathlib,sys; "
             f"assert os.getcwd()=={workspace!r}; "
             f"assert pathlib.Path('/workspace').stat().st_ino==pathlib.Path({workspace!r}).stat().st_ino; "
             "assert 'CapEff:\\t0000000000000000' in pathlib.Path('/proc/self/status').read_text(); "
             "assert not pathlib.Path('/sessions').exists(); "
             f"pathlib.Path('/workspace/{marker}').write_text('production-profile-ok'); "
             "print(sys.executable)")
    if is_repository_task(task):
        # Exercise the project's own editable import. Some upstream projects
        # (notably this SymPy revision) use a custom runner, not pytest.
        module = task.get("smoke_import", task.get("repo", task["id"].split("__")[0]).split("/")[-1])
        module = {"scikit-learn": "sklearn", "pytest-dev": "pytest", "sphinx-doc": "sphinx",
                  "pylint-dev": "pylint", "pydata": "xarray", "mwaskom": "seaborn", "pallets": "flask"}.get(module, module)
        probe += (f"; import importlib; module=importlib.import_module({module!r}); "
                  f"assert module.__file__.startswith({workspace + '/'!r}), module.__file__; print(module.__file__)")
    response = lambda content, stop: {"type": "message", "role": "assistant", "content": content,
        "stop_reason": stop, "usage": {"input_tokens": 1, "output_tokens": 1}}
    script = [response([{"type": "tool_use", "id": "probe", "name": "process",
                         "input": {"argv": ["python", "-c", probe]}},
                        {"type": "tool_use", "id": "read", "name": "read", "input": {"path": marker}}], "tool_use"),
              response([{"type": "text", "text": "preflight complete"}], "end_turn")]
    config = {"model": "scripted-preflight", "workspace": workspace, "commands": "allow",
              "executionProfile": "bubblewrap", "toolchainRoots": toolchain_roots(task),
              "operationTimeoutMs": 15000, "maxElapsedMs": 60000,
              "maxModelAttempts": 2, "maxToolCalls": 2}
    for name, value in [("script.json", script), ("config.json", config)]:
        (directory / name).write_text(json.dumps(value))
    docker("exec", container, "mkdir", "-p", "/agent/preflight", "/sessions")
    docker("cp", str(directory) + "/.", container + ":/agent/preflight")
    result = docker("exec", container, "/agent/harness", "run", "--workspace", workspace,
                    "--config", "/agent/preflight/config.json", "--script", "/agent/preflight/script.json",
                    "--task", "offline sandbox preflight", "--session", "/sessions/preflight", "--json",
                    timeout=75, output=directory / "events.log", check=False)
    inspection = docker("exec", container, "/agent/harness", "inspect", "/sessions/preflight", check=False)
    (directory / "inspection.json").write_text(inspection.stdout)
    observations = json.loads(inspection.stdout)["state"]["history"] if inspection.returncode == 0 else []
    tool_results = [block for message in observations for block in message["content"]
                    if block.get("type") == "tool_result"]
    passed = result.returncode == 0 and len(tool_results) == 2 and all(
        not block.get("is_error", False) for block in tool_results) and any(
            "production-profile-ok" in json.dumps(block) for block in tool_results)
    docker("exec", container, "rm", "-f", workspace + "/" + marker)
    report = {"passed": passed, "exit_code": result.returncode,
              "harness_binary_sha256": sha(harness_binary(args.harness_root)),
              "prepared_bwrap_sha256": args.bwrap_sha256, "toolchain_roots": toolchain_roots(task)}
    (directory / "result.json").write_text(json.dumps(report, indent=2) + "\n")
    if not passed:
        raise RuntimeError("production sandbox preflight failed; see profile-preflight evidence")
    return report


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


def regression_audit(directory, task_id):
    """Read the unchanged official per-instance test report, not just its score."""
    reports = list(Path(directory).glob("logs/evaluation/*/*/" + task_id + "/report.json"))
    if len(reports) != 1:
        return {"available": False, "reason": "expected one official per-instance report"}
    try:
        result = json.loads(reports[0].read_text())[task_id]
        status = result["tests_status"]
        counts = {name: {"passed": len(status[name]["success"]), "failed": len(status[name]["failure"])}
                  for name in ["FAIL_TO_PASS", "PASS_TO_PASS"]}
        return {"available": True, "test_counts": counts, "report_sha256": sha(reports[0])}
    except (KeyError, TypeError, ValueError):
        return {"available": False, "reason": "official per-instance test report shape changed"}


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
        regression = None
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
            before, after = regression_audit(target / "baseline", task["id"]), regression_audit(target / "reference", task["id"])
            regression = {"baseline": before, "reference": after, "passed": before["available"] and after["available"]
                and before["test_counts"]["FAIL_TO_PASS"]["failed"] > 0
                and before["test_counts"]["PASS_TO_PASS"]["failed"] == 0
                and after["test_counts"]["FAIL_TO_PASS"]["passed"] > 0
                and after["test_counts"]["FAIL_TO_PASS"]["failed"] == 0
                and after["test_counts"]["PASS_TO_PASS"]["failed"] == 0}
        profile = None
        if args.prepared_bwrap:
            container = None
            try:
                container = create_container(task["image_digest"], workspace=task["workspace"], nested_sandbox=True,
                    mounts=[(args.prepared_bwrap, "/usr/bin/bwrap", False),
                            (harness_binary(args.harness_root), "/agent/harness", False)])
                profile = production_smoke(task, container, args, target / "profile-preflight")
            except Exception as error:
                profile = {"passed": False, "infrastructure_error": type(error).__name__ + ": " + str(error)}
            finally:
                remove_container(container)
        records.append({"task_id": task["id"], "baseline": baseline, "reference": reference,
                        "docker_endpoint": docker_host(),
                        "production_profile": profile,
                        "regression_audit": regression,
                        "ready": not baseline.get("infrastructure_error") and not baseline["resolved"] and reference["resolved"]
                            and (profile is None or profile["passed"]) and (regression is None or regression["passed"])})
        (directory / "preflight.json").write_text(json.dumps(records, indent=2) + "\n")
        print(json.dumps(records[-1]), flush=True)
    return records


def run_invocations(container, first, resume, output, timeout, *, yield_after=0, max_invocations=128, host_harness=None):
    """Bounded subprocess restarts under one elapsed-time allowance."""
    deadline = time.monotonic() + timeout
    records, checkpoints = [], []
    combined = output / "events.log"
    combined.write_bytes(b"")
    for index in range(max_invocations):
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise subprocess.TimeoutExpired(first, timeout)
        invocation = list(first if index == 0 else resume)
        if yield_after:
            invocation += ["--yield-after", str(yield_after)]
        events = output / f"invocation-{index:03d}.jsonl"
        started = time.monotonic()
        exit_code = None
        try:
            completed = docker(*invocation, timeout=remaining, output=events, check=False)
            exit_code = completed.returncode
        finally:
            active_error = sys.exc_info()[1]
            record = {"invocation": index, "exit_code": exit_code,
                      "elapsed_seconds": round(time.monotonic() - started, 3), "events": events.name}
            records.append(record)
            try:
                with (output / "resources.jsonl").open("a") as stream:
                    stream.write(json.dumps(record) + "\n")
                if events.exists():
                    with combined.open("ab") as target, events.open("rb") as source:
                        shutil.copyfileobj(source, target, 65536)
            except Exception as diagnostic_error:
                if active_error is None:
                    raise
                # Preserve cancellation/timeout instead of replacing it with a
                # diagnostic write error and permitting another scheduled run.
                active_error.add_note("Invocation diagnostic write failed: " + type(diagnostic_error).__name__)
        if exit_code != 75:
            return {"exit_code": exit_code, "invocations": records, "durable_checkpoints": checkpoints}
        if not yield_after or resume is None:
            raise RuntimeError("unexpected suspension outside a declared restart trial")
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise subprocess.TimeoutExpired(first, timeout)
        trusted_harness = host_harness or harness_binary()
        session = output / "sessions/session"
        # The actual0600 journal remains root-owned in the prepared container.
        # Only already-flushed bytes enter this host-owned offline audit mirror.
        session.mkdir(mode=0o700, parents=True, exist_ok=True)
        journal = read_regular_file(container, "/sessions/session/journal.jsonl", 64 * 1024 * 1024,
                                    timeout_seconds=remaining)
        temporary = session / "journal.copying"
        temporary.write_bytes(journal)
        temporary.chmod(0o600)
        temporary.replace(session / "journal.jsonl")
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise subprocess.TimeoutExpired(first, timeout)
        inspected = command([trusted_harness, "inspect", session], timeout=min(30, remaining))
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise subprocess.TimeoutExpired(first, timeout)
        replayed = command([trusted_harness, "replay", session], timeout=min(30, remaining))
        (output / f"checkpoint-{index:03d}-inspection.json").write_text(inspected.stdout)
        (output / f"checkpoint-{index:03d}-replay.json").write_text(replayed.stdout)
        inspection = json.loads(inspected.stdout)
        if json.loads(replayed.stdout) != inspection or inspection.get("pending") or inspection.get("terminal"):
            raise RuntimeError("durable checkpoint replay differs or is not safely resumable")
        state = inspection["state"]
        checkpoint = {key: state[key] for key in ["nextId", "modelAttempts", "toolDispatches", "phase"]}
        if state.get("schemaVersion") == 7:
            if type(state.get("turn")) is not int or state["turn"] < 0:
                raise RuntimeError("schema7 checkpoint lacks a valid turn identity")
            checkpoint["turn"] = state["turn"]
        checkpoints.append(checkpoint | {"invocation": index,
            "summaries": len(state.get("summaries", [])), "replay_matches": True})
        (output / "durable-checkpoints.json").write_text(json.dumps(checkpoints, indent=2) + "\n")
    raise RuntimeError("declared restart invocation ceiling exhausted")


def validate_pi_settings(value, engine="pi"):
    """Validate the explicit mode data; the SDK preflight checks catalog/default bounds."""
    if not isinstance(value, dict) or set(value) - {"piContextWindow", "piCompaction"}:
        raise ValueError("unsupported Pi context settings")
    if value and engine != "pi":
        raise ValueError("Pi context settings require a Pi mode")
    def integer(number, minimum=0):
        return type(number) is int and minimum <= number <= 9007199254740991
    window = value.get("piContextWindow")
    if "piContextWindow" in value and not integer(window, 1):
        raise ValueError("piContextWindow must be a positive safe integer")
    if "piCompaction" in value:
        compaction = value["piCompaction"]
        if not isinstance(compaction, dict) or set(compaction) - {"enabled", "reserveTokens", "keepRecentTokens"}:
            raise ValueError("unsupported Pi compaction settings")
        if "enabled" in compaction and type(compaction["enabled"]) is not bool:
            raise ValueError("Pi compaction enabled must be Boolean")
        for field in ["reserveTokens", "keepRecentTokens"]:
            if field in compaction and not integer(compaction[field]):
                raise ValueError("Pi compaction token settings must be nonnegative safe integers")
            if field in compaction and window is not None and compaction[field] >= window:
                raise ValueError("Pi compaction token settings must be smaller than the context window")
        if window is not None and compaction.get("enabled", True) and sum(
                compaction.get(field, 0) for field in ["reserveTokens", "keepRecentTokens"]) >= window:
            raise ValueError("Pi compaction settings leave no context room")
    return json.loads(json.dumps(value))


def pi_terminal_observation(path):
    """Report the SDK wrapper's terminal counters without treating absent data as zero."""
    found = []
    with path.open() as stream:
        for line in stream:
            try:
                value = json.loads(line)
            except ValueError:
                continue
            if isinstance(value, dict) and value.get("type") == "evaluation_end":
                found.append(value)
                if len(found) > 1:
                    break
    if len(found) != 1:
        return {"tool_dispatches": None, "pi_terminal_observation": None,
                "pi_terminal_observation_error": "missing or duplicate evaluation_end"}
    event = found[0]
    count = event.get("toolDispatches")
    return {"tool_dispatches": count if type(count) is int and count >= 0 else None,
            "pi_terminal_observation": {key: event.get(key) for key in ["normalFinish", "stopReason", "error"]},
            **({"pi_context_configuration": event["piContextConfiguration"]}
               if "piContextConfiguration" in event else {})}


def capture_stopped_evidence(container, workspace, baseline, output, sessions, engine, args, broker, record):
    """Retain stopped bytes independently; failed capture never means an empty patch.

    Only trusted host archive readers and offline Lean inspection run here. This
    also runs while unwinding an interruption, before exact-owned deletion; it
    does not invoke a grader or execute anything inside the candidate.
    """
    capture = record.setdefault("evidence_capture", {})
    if "session" not in capture:
        try:
            staging = output / "session-copy-staging"
            record["session_mirror"] = mirror_session_after_stop(container, "/sessions", staging)
            if sessions.exists():
                sessions.rename(output / "checkpoint-session-mirror")
            staging.rename(sessions)
            if (output / "checkpoint-session-mirror").exists():
                shutil.rmtree(output / "checkpoint-session-mirror")
            capture["session"] = {"status": "captured", "path": str(sessions)}
        except Exception as error:
            capture["session"] = {"status": "unavailable", "error": type(error).__name__ + ": " + str(error)}
            record["evidence_capture_unsettled"] = True

    # A missing/corrupt session must not prevent retaining the workspace bytes.
    if "workspace" not in capture:
        try:
            if baseline is None:
                raise RuntimeError("trusted baseline was not captured; candidate patch is unknown")
            snapshot = capture_candidate_after_stop(container, workspace, output / "candidate-snapshot", baseline)
            record["workspace_snapshot"] = snapshot
            patch = Path(snapshot["patch_path"]).read_bytes()
            (output / "candidate.patch").write_bytes(patch)
            record["candidate_patch_sha256"] = sha(output / "candidate.patch")
            changed = snapshot["changed_paths"]
            record["test_files_modified"] = [name for name in changed if any(
                part == "tests" or part.startswith("test_") for part in Path(name).parts)]
            record["existing_test_files_modified"] = [name for name in snapshot["existing_changed_paths"] if any(
                part in {"test", "tests", "testing", "conftest.py"} or part.startswith("test_") for part in Path(name).parts)]
            capture["workspace"] = {"status": "captured", "patch_sha256": record["candidate_patch_sha256"]}
        except Exception as error:
            capture["workspace"] = {"status": "unavailable", "error": type(error).__name__ + ": " + str(error)}
            record["evidence_capture_unsettled"] = True

    if record.get("evidence_capture_unsettled"):
        record.setdefault("infrastructure_error", "stopped candidate evidence capture was incomplete")
    if engine == "lean" and capture["session"]["status"] == "captured":
        try:
            inspected = command([harness_binary(args.harness_root), "inspect", sessions / "session"], check=False)
            (output / "inspection.json").write_text(inspected.stdout)
            if inspected.returncode:
                raise AuditError("retained session inspection failed")
            inspection = json.loads(inspected.stdout)
            state = inspection["state"]
            record.update(model_attempts=state["modelAttempts"], tool_dispatches=state["toolDispatches"],
                          summaries=len(state.get("summaries", [])), unknown_usage=state["unknownUsage"])
            replayed = command([harness_binary(args.harness_root), "replay", sessions / "session"], check=False)
            (output / "replay.json").write_text(replayed.stdout)
            replay = json.loads(replayed.stdout)
            record["replay_matches"] = replayed.returncode == 0 and replay == inspection
            record["session_integrity"] = completed_session(output, inspection, replay,
                [charge for charge in broker.records if charge["run_id"] == record["run_id"]],
                normal=record.get("exit_code") == 0, request_evidence_version=REQUEST_EVIDENCE_VERSION)
        except Exception as error:
            record["session_integrity"] = {"passed": False, "reason": str(error)}


def record_broker_close_failure(record, broker, run_id, error):
    """Keep failed evidence persistence separate from durable charge settlement."""
    with broker.lock:
        storage = dict(broker.storage_failure) if broker.storage_failure is not None else None
        unsettled = any(row.get("accounting_settled") is not True
                        for row in broker.records if row["run_id"] == run_id)
    record.update(success=False, accounting_unsettled=unsettled,
                  broker_close_failure={"error": type(error).__name__, "detail": str(error)})
    if storage is not None:
        record["broker_storage_failure"] = storage
        reason = "broker evidence storage failed"
        if unsettled:
            reason += "; provider accounting also did not settle"
    else:
        reason = "provider accounting did not settle" if unsettled else "broker close failed"
    record["infrastructure_error"] = reason + ": " + type(error).__name__


def cohort_stop_reason(record):
    return ("runtime prerequisite failed" if record.get("runtime_prerequisite_failed") else
            "broker evidence storage failed" if record.get("broker_storage_failure") else
            "provider accounting did not settle" if record.get("accounting_unsettled") else
            "broker close failed" if record.get("broker_close_failure") else
            "candidate cleanup did not settle" if record.get("cleanup_unsettled") else
            "spending admission refused" if record.get("admission_refused") else
            "initial task request evidence failed" if record.get("initial_task_request_evidence", {}).get("passed") is False else None)


def run_one(task, engine, repetition, rows, args, directory, broker, *, task_text=None, verify_patch=None):
    if not is_repository_task(task):
        raise RuntimeError("paid execution currently supports repository snapshots only; legacy Terminal-Bench extraction is not qualified")
    run_id = f"{task['id']}-{engine}-{repetition}-{uuid.uuid4().hex[:8]}"
    output = directory / run_id
    output.mkdir(mode=0o700)
    sessions = output / "sessions"
    sessions.mkdir()
    registered = False
    close_error = None
    workspace = task["workspace"]
    if task_text is not None:
        prompt = task_text
    elif task["benchmark"].startswith("terminal"):
        prompt = (args.tb_repo / task["source_path"] / "instruction.md").read_text()
    else:
        prompt = next(r["problem_statement"] for r in rows if r["instance_id"] == task["id"])
    source_prompt = prompt
    prompt += "\n\nTask requirements:\n" + TASK_CONSTRAINTS
    instructions = (f"You are a coding agent working in {workspace}. Inspect the available files, complete the task, "
                    "run relevant checks, and explain the result. Read before editing and use the returned SHA256 preimage. "
                    "Follow the task requirements, including the shared test-preservation and review policy. "
                    "The environment is disposable and command execution is allowed. Work within the task workspace.")
    config = {"model": args.model, "workspace": workspace, "instructions": instructions, "commands": "allow",
              "maxModelAttempts": args.max_attempts, "maxToolCalls": args.max_tools,
              "maxContextBytes": args.context_bytes,
              "maxOutputTokens": getattr(args, "max_output_tokens", 4096), "maxRetries": 0,
              "maxResponseRepairs": getattr(args, "response_repairs", 2),
              "operationTimeoutMs": 90000, "maxElapsedMs": args.timeout * 1000,
              "maxToolOutputBytes": 16384, "testEndpoint": "", "compactionEnabled": True}
    overrides = getattr(args, "config_overrides", {})
    allowed_overrides = {"compactAtPercent", "compactionKeepMessages", "maxSummaryBytes", "maxOutputTokens", "maxToolOutputBytes", "maxResponseRepairs"}
    if set(overrides) - allowed_overrides:
        raise ValueError("unsupported sustained-mode configuration override")
    config.update(overrides)
    config["maxOutputTokens"] = output_ceiling(config["maxOutputTokens"])
    pi_settings = validate_pi_settings(getattr(args, "pi_settings", {}), engine)
    if engine == "lean" and args.prepared_bwrap:
        config.update(executionProfile="bubblewrap", toolchainRoots=toolchain_roots(task))
    (output / "config.json").write_text(json.dumps(config))
    (output / "pi-config.json").write_text(json.dumps({**config, **pi_settings, "task": prompt, "track": "product",
        "sessionDir": "/sessions", "toolBinary": "/agent/eval_tools", "schemasPath": "/agent/schemas.json"}))
    mounts = [(harness_binary(args.harness_root), "/agent/harness", False),
              (eval_tools_binary(args.harness_root), "/agent/eval_tools", False),
              (ROOT / "baseline", "/baseline", False),
              (directory / "schemas.json", "/agent/schemas.json", False),
              (output / "config.json", "/agent/config.json", False),
              (output / "pi-config.json", "/agent/pi-config.json", False)]
    if engine == "lean" and args.prepared_bwrap:
        mounts.append((args.prepared_bwrap, "/usr/bin/bwrap", False))
    record = {"run_id": run_id, "task_id": task["id"], "benchmark": task["benchmark"],
              "docker_endpoint": docker_host(),
              "engine": engine, "track": "product", "repetition": repetition, "success": False,
              "cohort": args.cohort or task.get("cohort", "original-preselection"),
              "mode": getattr(args, "mode_id", "product"),
              "attempt": args.attempt, "apt_https": args.apt_https, "apt_main_only": args.apt_main_only,
              "source_task_sha256": hashlib.sha256(source_prompt.encode()).hexdigest(),
              "user_task_sha256": hashlib.sha256(prompt.encode()).hexdigest(),
              "request_evidence_version": REQUEST_EVIDENCE_VERSION,
              "qualification_version": QUALIFICATION_VERSION,
              "qualification_status": "pending_independent_review",
              "requires_continuation_audit": bool(getattr(args, "yield_after", 0)),
              "image_digest": task["image_digest"], "model": args.model,
              "max_output_tokens": config["maxOutputTokens"]}
    if pi_settings:
        record["pi_context_settings"] = pi_settings
    container, artifact, baseline = None, None, None
    candidate_stopped = False
    started = time.monotonic()
    try:
        assert_space()
        try:
            node = node_identity()
        except Exception:
            record["runtime_prerequisite_failed"] = True
            raise
        record["node_identity"] = node
        mounts.append((Path(node["root"]), "/opt/node", False))
        container = create_container(task["image_digest"], workspace=workspace, mounts=mounts,
                                     nested_sandbox=engine == "lean" and bool(args.prepared_bwrap))
        docker("exec", container, "mkdir", "-p", "/sessions")
        if args.apt_https:
            apt_https(container, args.apt_main_only)
        # curl is a transport dependency absent from the two official TB bases;
        # retain the exact package list and image ID, while leaving tasks intact.
        docker("exec", container, "/bin/bash", "-lc",
               "command -v /usr/bin/curl >/dev/null || (apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y curl)",
               timeout=180, output=output / "transport-setup.log")
        if is_repository_task(task):
            # Discard solution-bearing remote history before either agent runs.
            docker("exec", "-w", workspace, container, "/bin/bash", "-lc",
                   "rm -rf .git && git init -q && git add . && git -c user.name=Evaluation -c user.email=evaluation@localhost commit -qm baseline",
                   timeout=90, output=output / "repository-setup.log")
            baseline = capture_baseline(container, workspace, output / "baseline-snapshot")
            record["workspace_baseline_tree"] = baseline["baseline_tree"]
        if engine == "lean" and args.prepared_bwrap:
            record["production_profile"] = production_smoke(task, container, args, output / "profile-preflight")
        if engine == "pi":
            try:
                startup = docker("exec", "-w", workspace, container, "/opt/node/bin/node",
                                 "/baseline/preflight.mjs", args.model, workspace, "/sessions/pi-preflight",
                                 *(["/agent/pi-config.json"] if pi_settings else []),
                                 timeout=30)
                (output / "pi-startup.log").write_text(startup.stdout)
                record["pi_startup_preflight"] = validate_node_preflight(startup.stdout, node, args.model)
            except Exception:
                record["runtime_prerequisite_failed"] = True
                raise
        endpoint = broker.add_run(run_id, args.max_attempts, args.context_bytes + 24000,
                                  config["maxOutputTokens"])
        registered = True
        config["testEndpoint"] = endpoint
        (output / "config.json").write_text(json.dumps(config))
        (output / "pi-config.json").write_text(json.dumps({**config, **pi_settings, "task": prompt, "track": "product",
            "sessionDir": "/sessions", "toolBinary": "/agent/eval_tools", "schemasPath": "/agent/schemas.json"}))
        path = "/opt/node/bin:/opt/miniconda3/envs/testbed/bin:/usr/local/bin:/usr/bin:/bin"
        invocation = ["exec", "-w", workspace, "-e", "PATH=" + path, container]
        if engine == "lean":
            invocation += ["/agent/harness", "run", "--workspace", workspace, "--config", "/agent/config.json",
                           "--task", prompt, "--session", "/sessions/session", "--json"]
            resume = ["exec", "-w", workspace, "-e", "PATH=" + path, container,
                      "/agent/harness", "resume", "/sessions/session", "--json"]
        else:
            invocation += ["/opt/node/bin/node", "/baseline/run.mjs", "/agent/pi-config.json"]
            resume = None
        memory = ContainerMemory(container).start()
        agent_started = time.monotonic()
        record["preparation_seconds"] = round(agent_started - started, 3)
        try:
            record.update(run_invocations(container, invocation, resume, output, args.timeout,
                yield_after=getattr(args, "yield_after", 0) if engine == "lean" else 0,
                max_invocations=getattr(args, "max_invocations", 128), host_harness=harness_binary(args.harness_root)))
        except subprocess.TimeoutExpired:
            record["timed_out"] = True
            record["exit_code"] = None
        finally:
            record["agent_elapsed_seconds"] = round(time.monotonic() - agent_started, 3)
            # A damaged diagnostic must not replace an in-flight KeyboardInterrupt
            # and accidentally permit the caller to continue its schedule.
            try:
                record["memory"] = memory.stop()
                if (output / "durable-checkpoints.json").exists():
                    record["durable_checkpoints"] = json.loads((output / "durable-checkpoints.json").read_text())
                if (output / "resources.jsonl").exists():
                    record["invocations"] = [json.loads(line) for line in (output / "resources.jsonl").read_text().splitlines()]
                if engine == "pi" and (output / "events.log").exists():
                    record.update(pi_terminal_observation(output / "events.log"))
            except Exception as error:
                record["invocation_metadata_error"] = type(error).__name__ + ": " + str(error)
                record.setdefault("infrastructure_error", "invocation metadata could not be read")
        record["elapsed_seconds"] = round(time.monotonic() - started, 3)
        docker("stop", "--time", "1", container)
        candidate_stopped = True
        if registered:
            try:
                broker.close_run(run_id)
            except Exception as error:
                close_error = error
                record_broker_close_failure(record, broker, run_id, error)
        capture_stopped_evidence(container, workspace, baseline, output, sessions, engine, args, broker, record)
        if record.get("timed_out") or record["evidence_capture"]["workspace"]["status"] != "captured":
            return record
        if is_repository_task(task):
            patch = (output / "candidate.patch").read_text()
            prediction = {"instance_id": task["id"], "model_name_or_path": engine + "-product", "model_patch": patch}
            (output / "predictions.jsonl").write_text(json.dumps(prediction) + "\n")
            verdict = (verify_patch(task, prediction, output / "verification") if verify_patch is not None else
                       swe_verify(task, prediction, rows, args.swe_python, output / "verification"))
        else:
            docker("cp", container + ":" + workspace + "/.", output / "workspace")
            verdict = tb_verify(task, task["image_digest"], args.tb_repo, output / "verification", output / "workspace",
                                args.apt_https, args.apt_main_only)
        record["checker"] = verdict
        if verdict.get("infrastructure_error"):
            record["infrastructure_error"] = verdict["infrastructure_error"]
        # Qualification is deliberately deferred to an independent host review.
        # Raw upstream, completion and integrity evidence remain separate.
        record["artifact_pass"] = verdict.get("resolved") is True
        record["normal_finish"] = record["exit_code"] == 0
    except BaseException as error:
        record["infrastructure_error"] = type(error).__name__ + ": " + str(error)
        if getattr(error, "__notes__", None):
            record["invocation_diagnostic_errors"] = list(error.__notes__)
        if not isinstance(error, Exception):
            record.update(interrupted=True, interruption=type(error).__name__, exit_code=None)
            raise
    finally:
        if container and not candidate_stopped:
            try:
                docker("stop", "--time", "1", container)
                candidate_stopped = True
            except Exception as error:
                record.update(success=False, cleanup_failure=type(error).__name__)
                # Do not wait for provider settlement with a potentially active candidate.
                try:
                    docker("rm", "-f", container)
                    container = None
                except Exception as removal:
                    record["cleanup_failure"] += "; forced removal: " + type(removal).__name__
                    record["cleanup_unsettled"] = True
        if registered:
            try:
                broker.close_run(run_id)
            except Exception as error:
                close_error = error
            if close_error is not None:
                # A timed-out first close may settle during evidence capture.
                # Keep the close failure, but report the latest charge status.
                record_broker_close_failure(record, broker, run_id, close_error)
            refusal = broker.admission_refusal(run_id)
            if refusal is not None:
                record.update(success=False, admission_refused=refusal)
        if any(kind not in record.get("evidence_capture", {}) for kind in ("session", "workspace")):
            if container and candidate_stopped:
                capture_stopped_evidence(container, workspace, baseline, output, sessions, engine, args, broker, record)
            else:
                record["evidence_capture_unsettled"] = True
                record["evidence_capture"] = {kind: {"status": "unavailable", "error":
                    "candidate stop/capture boundary unavailable; retained bytes are unknown"}
                    for kind in ("session", "workspace")}
        try:
            remove_container(container)
        except Exception as error:
            record.update(success=False, cleanup_unsettled=True,
                          infrastructure_error="candidate cleanup failed: " + type(error).__name__)
        if artifact:
            docker("image", "rm", artifact, check=False)
        if ACTIVE_OWNER is not None:
            record['owned_container_cleanup'] = ACTIVE_OWNER.cleanup()
            record['official_swe_grader_ownership'] = 'Not covered: official evaluator may create containers through its own SDK.'
            if ACTIVE_OWNER.uncertain or not record['owned_container_cleanup']['settled']:
                record.update(success=False, cleanup_unsettled=True,
                              infrastructure_error='owned-container journal or cleanup did not settle')
        charged = [r for r in broker.records if r["run_id"] == run_id]
        record.update(provider_attempts=len(charged), accounted_usd=sum(r["charged_usd"] for r in charged),
                      unknown_usage_requests=sum(r["usage"] is None for r in charged))
        try:
            record["initial_task_request_evidence"] = audit_initial_task(charged, record["user_task_sha256"])
        except AuditError as error:
            record["initial_task_request_evidence"] = {"passed": False, "reason": str(error)}
        record["response_evidence_failures"] = [{"attempt": row["attempt"], "evidence": row["response_evidence"]}
            for row in charged if row.get("response_evidence", {}).get("status") == "storage_failed"]
        record["artifact_pass"] = record.get("checker", {}).get("resolved") is True
        record["automated_qualification_checks"] = automated_checks(record)
        record["normal_finish"] = record["automated_qualification_checks"]["normal_finish"]
        (output / "result.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def unrun_slot(task_id, engine, repetition, reason, **extra):
    """Keep every declared slot visible when accounting closes a cohort early."""
    return {"task_id": task_id, "engine": engine, "repetition": repetition,
            "success": False, "not_run": True, "provider_attempts": 0, "accounted_usd": 0,
            "unrun_reason": reason, **extra}


def main():
    global ACTIVE_OWNER
    parser = argparse.ArgumentParser(description=__doc__)
    add_harness_root_argument(parser)
    parser.add_argument("--campaign-dir", type=Path)
    parser.add_argument("--allocation")
    parser.add_argument("mode", choices=["preflight", "run"])
    parser.add_argument("--lock", type=Path, default=LOCK_PATH, help="Explicit task lock; historical locks are never rewritten")
    parser.add_argument("--prepared-bwrap", type=Path, help="Compatible non-setuid Bubblewrap build for the official image")
    parser.add_argument("--bwrap-sha256", help="Required exact digest of --prepared-bwrap")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--tb-repo", type=Path, default=Path("/tmp/lean-harness-terminal-bench-2-1"))
    parser.add_argument("--swe-python", type=Path, default=Path("/tmp/lean-harness-swebench-venv/bin/python"))
    parser.add_argument("--dataset", type=Path, default=Path("/tmp/lean-harness-public-preflight/swe-dataset.json"))
    parser.add_argument("--tasks", nargs="*")
    parser.add_argument("--engines", nargs="+", choices=["lean", "pi"], default=["lean", "pi"])
    parser.add_argument("--key-file", type=Path)
    parser.add_argument("--retain-responses", action="store_true", help="Retain bounded host-only response evidence for diagnostics")
    parser.add_argument("--budget", type=float, default=35)
    parser.add_argument("--model", default="claude-opus-5-5")
    parser.add_argument("--repetitions", type=int, default=1)
    parser.add_argument("--repetition-start", type=int, default=0)
    parser.add_argument("--attempt", type=int, default=1)
    parser.add_argument("--apt-https", action="store_true", help="Record an opt-in Ubuntu repository transport repair")
    parser.add_argument("--apt-main-only", action="store_true", help="With --apt-https, fetch only main package indexes for curl setup")
    parser.add_argument("--cohort", help="Explicit label for a separately authorized diagnostic cohort")
    parser.add_argument("--max-attempts", type=int, default=12)
    parser.add_argument("--max-output-tokens", type=int, default=4096,
                        help="Frozen per-run output ceiling, 1..8192; default 4096")
    parser.add_argument("--response-repairs", type=int, default=2)
    parser.add_argument("--task-context-version", type=int, choices=[1, 2, 3, 4], default=1,
                        help="Frozen Lean context: legacy1, budget-notice2, command-time-limit3, application-context4")
    parser.add_argument("--max-tools", type=int, default=24)
    parser.add_argument("--context-bytes", type=int, default=120000)
    parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args()
    try:
        output_ceiling(args.max_output_tokens)
    except ValueError as error:
        parser.error(str(error))
    if args.response_repairs < 0:
        parser.error("--response-repairs must be nonnegative")
    try:
        sandbox = prepared_sandbox(args)
    except RuntimeError as error:
        parser.error(str(error))
    if args.mode == "run" or args.prepared_bwrap:
        if args.campaign_dir is None or args.allocation is None:
            if args.mode == "run":
                parser.error("run requires --campaign-dir and --allocation")
        try:
            args.harness_root = harness_root(args.harness_root)
            require_fresh_harness(args.harness_root)
            if args.mode == "run":
                eval_tools_binary(args.harness_root)
                node_root()
        except RuntimeError as error:
            parser.error(str(error))
    if args.apt_main_only and not args.apt_https:
        parser.error("--apt-main-only requires --apt-https")
    directory = args.output.resolve()
    directory.mkdir(mode=0o700, parents=True, exist_ok=False)
    ACTIVE_OWNER = Owner(directory)
    lock = json.loads(args.lock.read_text())
    if args.mode == "run" and any(not is_repository_task(task) for task in tasks(lock)
                                 if not args.tasks or task["id"] in args.tasks):
        parser.error("legacy Terminal-Bench paid execution is disabled pending qualified artifact export; historical reports remain available")
    if args.mode == "run" and str(lock.get("status", "")).startswith("DRAFT"):
        parser.error("draft task locks permit offline preflight only; freeze the reviewed protocol before paid execution")
    required_bwrap = lock.get("prepared_runtime", {}).get("bwrap_binary_sha256")
    if required_bwrap and ((args.mode == "run" and not args.prepared_bwrap) or
                           (args.prepared_bwrap and args.bwrap_sha256 != required_bwrap)):
        parser.error("prepared runtime differs from the reviewed task lock")
    shutil.copyfile(args.lock, directory / "public-lock.json")
    rows = check_assets(lock, args.tb_repo, args.dataset, args.swe_python, args.tasks)
    if args.mode == "preflight":
        results = preflight(lock, rows, args, directory)
        return 0 if all(r["ready"] for r in results) else 1
    if args.key_file is None:
        parser.error("run requires --key-file")
    (directory / "schemas.json").write_bytes(subprocess.check_output([str(eval_tools_binary(args.harness_root)), "schemas"]))
    (directory / "plan.json").write_text(json.dumps({"public_lock_sha256": sha(args.lock),
        "binary_sha256": sha(harness_binary(args.harness_root)), "tool_binary_sha256": sha(eval_tools_binary(args.harness_root)),
        "pi_lock_sha256": sha(ROOT / "baseline/package-lock.json"), "model": args.model,
        "tool_schemas_sha256": sha(directory / "schemas.json"),
        "runner_sha256": sha(__file__), "paths_sha256": sha(ROOT / "runner/paths.py"),
        **product_provenance(args.harness_root), **evaluation_provenance(), "created_unix": time.time(),
        "budget_usd": args.budget, "retain_responses": args.retain_responses, "repetitions": args.repetitions, "max_attempts": args.max_attempts,
        "max_response_repairs": args.response_repairs, "task_context_version": args.task_context_version,
        "max_output_tokens": args.max_output_tokens,
        "request_evidence_version": REQUEST_EVIDENCE_VERSION,
        "repetition_start": args.repetition_start,
        "attempt": args.attempt, "apt_https": args.apt_https, "apt_main_only": args.apt_main_only,
        "cohort": args.cohort,
        "execution_profile": sandbox or {"profile": "historical outer-container only"},
        "shared_user_constraints": TASK_CONSTRAINTS,
        "shared_user_constraints_sha256": hashlib.sha256(TASK_CONSTRAINTS.encode()).hexdigest(),
        "snapshot_limits": SNAPSHOT_LIMITS, "snapshot_exclusions": SNAPSHOT_EXCLUSIONS,
        "session_mirror_limits": SESSION_LIMITS,
        "session_audit_provenance": "regular-only host audit mirrors; original journals reside in prepared container during execution",
        "qualification_version": QUALIFICATION_VERSION,
        "qualification_rule": QUALIFICATION_RULE,
        "max_tools": args.max_tools, "context_bytes": args.context_bytes, "track": "product",
        "timeout_seconds": args.timeout, "tasks": args.tasks or [t["id"] for t in tasks(lock)], "engines": args.engines}, indent=2))
    results = []
    with Broker(args.key_file.expanduser().read_text().strip(), directory, args.budget, args.model,
                campaign=args.campaign_dir, allocation=args.allocation, retain_responses=args.retain_responses) as broker:
        scheduled = [(task, engine, repetition)
            for repetition in range(args.repetition_start, args.repetition_start + args.repetitions)
            for index, task in enumerate(tasks(lock)) if not args.tasks or task["id"] in args.tasks
            for engine in (args.engines if (index + repetition) % 2 == 0 else list(reversed(args.engines)))]
        for slot, (task, engine, repetition) in enumerate(scheduled):
            if task.get("preflight_status") == "ineligible":
                result = unrun_slot(task["id"], engine, repetition, "preflight infrastructure exclusion",
                                    infrastructure_error=task["preflight_reason"])
            else:
                result = run_one(task, engine, repetition, rows, args, directory, broker)
            results.append(result)
            stop_reason = cohort_stop_reason(result)
            if stop_reason:
                results.extend(unrun_slot(next_task["id"], next_engine, next_rep, stop_reason)
                               for next_task, next_engine, next_rep in scheduled[slot + 1:])
            (directory / "results.json").write_text(json.dumps(results, indent=2) + "\n")
            print(json.dumps({key: result.get(key) for key in ["task_id", "engine", "artifact_pass", "normal_finish", "qualification_status", "provider_attempts", "accounted_usd", "infrastructure_error", "admission_refused"]}), flush=True)
            if stop_reason:
                return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
