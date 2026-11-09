#!/usr/bin/env python3
"""One bounded live coding task. Requires Linux bubblewrap; never logs credentials.

This is development evidence, not a held-out benchmark. Only the fixture workspace
is exposed to the model. The checker is mounted in separate post-run processes.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]


def native_source_hashes():
    inputs = [ROOT / "rust-toolchain.toml", ROOT / "lakefile.lean",
              ROOT / "runtime/native/Cargo.toml", ROOT / "runtime/native/Cargo.lock",
              ROOT / "runtime/native/build.rs"]
    inputs += sorted((ROOT / "runtime/native/src").rglob("*.rs"))
    return {path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in inputs}


def sandbox(workspace, extra_mounts=()):
    cmd = ["bwrap", "--unshare-all", "--share-net", "--die-with-parent", "--new-session"]
    for path in ["/usr", "/lib", "/lib64", "/etc/ssl", "/etc/resolv.conf", "/etc/hosts", "/etc/nsswitch.conf"]:
        if Path(path).exists():
            cmd += ["--ro-bind", path, path]
    cmd += ["--symlink", "/usr/bin", "/bin", "--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp",
            "--bind", str(workspace), "/workspace", "--chdir", "/workspace"]
    for source, dest, writable in extra_mounts:
        cmd += ["--bind" if writable else "--ro-bind", str(source), dest]
    return cmd


def child_environment(key=None):
    env = {"PATH": "/usr/bin:/bin", "HOME": "/tmp", "LANG": "C.UTF-8", "PYTHONDONTWRITEBYTECODE": "1"}
    if key:
        env["ANTHROPIC_API_KEY"] = key
    return env


def check(workspace, output, label):
    checker = ROOT / "eval/tasks/ranges_check.py"
    result = subprocess.run(sandbox(workspace, [(checker, "/checker.py", False), (ROOT / "eval/tasks/ranges", "/ranges", False)]) +
        ["/usr/bin/python3", "-I", "-S", "/checker.py", "/workspace"],
        env=child_environment(), capture_output=True, text=True, timeout=30)
    (output / f"{label}-check.stdout").write_text(result.stdout)
    (output / f"{label}-check.stderr").write_text(result.stderr)
    try:
        report = json.loads(result.stdout)
    except ValueError:
        raise RuntimeError(f"{label} checker did not return valid JSON; inspect private check logs")
    if result.returncode not in (0, 1) or report.get("passed") != (result.returncode == 0):
        raise RuntimeError(f"{label} checker infrastructure failure")
    return result.returncode


def run(args):
    binary = ROOT / ".lake/build/bin/harness"
    if not binary.is_file() or shutil.which("bwrap") is None:
        raise RuntimeError("run lake build and install bubblewrap before the live smoke test")
    key = Path(args.key_file).expanduser().read_text().strip() if args.key_file else os.environ.get("ANTHROPIC_API_KEY", "")
    if not key:
        raise RuntimeError("provide ANTHROPIC_API_KEY or --key-file")
    output = Path(args.output).resolve() if args.output else Path(tempfile.mkdtemp(prefix="lean-harness-live-"))
    if args.output:
        output.mkdir(mode=0o700, parents=True, exist_ok=False)
    os.chmod(output, 0o700)
    workspace = output / "workspace"
    shutil.copytree(ROOT / "eval/tasks/ranges", workspace)
    subprocess.run(["git", "init", "-q", str(workspace)], check=True)
    subprocess.run(["git", "-C", str(workspace), "add", "."], check=True)
    subprocess.run(["git", "-C", str(workspace), "-c", "user.name=Harness evaluation", "-c",
                    "user.email=harness@example.invalid", "commit", "-qm", "Seeded development task"], check=True)
    sessions = output / "sessions"
    sessions.mkdir(mode=0o700)
    config = {
        "model": args.model, "workspace": "/workspace", "commands": "allow",
        "instructions": "You are a coding agent working on a small repository. Inspect the README and source files, implement the stated behavior, run the existing tests, and explain your changes. Work only in /workspace. Do not modify tests or the README. Use read before edit and supply the returned SHA256 preimage. Keep the solution simple.",
        "maxModelAttempts": 10, "maxToolCalls": 24, "maxContextBytes": 150000,
        "maxOutputTokens": 4096, "maxRetries": 1, "operationTimeoutMs": 90000,
        "maxElapsedMs": 300000,
    }
    config_file = output / "config.json"
    config_file.write_text(json.dumps(config, indent=2) + "\n")
    baseline = check(workspace, output, "baseline")
    if baseline == 0:
        raise RuntimeError("baseline unexpectedly passes independent checker")
    mounts = [(binary, "/app/.lake/build/bin/harness", False),
              (config_file, "/config.json", False), (sessions, "/sessions", True)]
    command = sandbox(workspace, mounts) + ["/app/.lake/build/bin/harness", "run", "--workspace", "/workspace",
        "--config", "/config.json", "--task", "Fix parse_ranges to satisfy README.md. Run the existing tests and explain the fix.",
        "--session", "/sessions/session", "--json"]
    print(json.dumps({"event": "started", "model": args.model, "output": str(output)}), flush=True)
    start = time.monotonic()
    timed_out = False
    with open(output / "events.jsonl", "w") as events, open(output / "diagnostics.txt", "w") as diagnostics:
        process = subprocess.Popen(command, env=child_environment(key), stdout=events, stderr=diagnostics, start_new_session=True)
        try:
            exit_code = process.wait(timeout=420)
        except subprocess.TimeoutExpired:
            timed_out = True
            if (sessions / "session").is_dir():
                (sessions / "session/cancel").write_text("watchdog\n")
            try:
                exit_code = process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                exit_code = process.wait()
    elapsed = round(time.monotonic() - start, 3)
    check_exit = check(workspace, output, "final")
    immutable = all((workspace / name).read_bytes() == (ROOT / "eval/tasks/ranges" / name).read_bytes()
                    for name in ["test_ranges.py", "README.md"])
    inspected = subprocess.run(sandbox(workspace, mounts) + ["/app/.lake/build/bin/harness", "inspect", "/sessions/session"],
                               env=child_environment(), capture_output=True, text=True, timeout=30)
    state = {}
    inspection_ok = inspected.returncode == 0
    if inspection_ok:
        state = json.loads(inspected.stdout)["state"]
        (output / "inspection.json").write_text(inspected.stdout)
    else:
        (output / "inspection-error.txt").write_text(inspected.stderr)
    summary = {"model": args.model, "harness_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
        "native_sources_sha256": native_source_hashes(),
        "checker_sha256": hashlib.sha256((ROOT / "eval/tasks/ranges_check.py").read_bytes()).hexdigest(),
        "fixture_sha256": {name: hashlib.sha256((ROOT / "eval/tasks/ranges" / name).read_bytes()).hexdigest()
                           for name in ["README.md", "test_ranges.py", "ranges.py"]},
        "dirty_source_tree": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True)),
        "baseline_checker_exit": baseline, "harness_exit": exit_code, "checker_exit": check_exit,
        "fixture_tests_unchanged": immutable, "elapsed_seconds": elapsed, "watchdog_fired": timed_out,
        "inspection_ok": inspection_ok, "model_attempts": state.get("modelAttempts"),
        "tool_dispatches": state.get("toolDispatches"), "known_input_tokens": state.get("knownInputTokens"),
        "known_output_tokens": state.get("knownOutputTokens"), "unknown_usage_observations": state.get("unknownUsage"),
        "phase": state.get("phase"), "success": exit_code == 0 and check_exit == 0 and immutable and inspection_ok and not timed_out}
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2), flush=True)
    return 0 if summary["success"] else 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model", default="claude-opus-5-5")
    parser.add_argument("--key-file", help="Local credential file; contents are never logged")
    parser.add_argument("--output", help="New directory for private session evidence (default: temporary directory)")
    try:
        raise SystemExit(run(parser.parse_args()))
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        # Do not include request headers, credentials, or the inherited environment.
        print(json.dumps({"error": str(error)}))
        raise SystemExit(2)
