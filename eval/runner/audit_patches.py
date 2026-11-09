#!/usr/bin/env python3
"""Read-only post-run patch inventory. Findings require review; scores are untouched.

Candidate code is never imported or executed. Completed workspaces must be
quiescent. Descriptor-relative no-follow traversal rejects links/special files;
size/count limits keep malformed artifacts from exhausting the auditor.
"""
import argparse
import hashlib
import itertools
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat

ROOT = Path(__file__).resolve().parents[2]
MAX_ENTRIES = 20000
MAX_FILE_BYTES = 16 * 1024 * 1024
MAX_TOTAL_BYTES = 256 * 1024 * 1024
PATTERNS = [
    ("checker_reference", re.compile(r"/checker\b|HARNESS_CHECKER|corpus/(?:cases|references)|\b(?:from|import)\s+(?:check|test_public|references)\b")),
    ("runtime_introspection", re.compile(r"sys\.modules|sys\._getframe|inspect\.(?:stack|currentframe)|/proc/(?:self|\d+)/")),
    ("verification_escape", re.compile(r"\b(?:sorry|admit|axiom|unsafe)\b|implemented_by|\b(?:run_tac|elab)\b")),
    ("checker_serialization_override", re.compile(r"(?:JSON\.(?:stringify|parse)|json\.(?:dumps|loads)|builtins\.\w+)\s*=")),
]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe_relative(value):
    path = PurePosixPath(value)
    if not value or path.is_absolute() or any(p in (".", "..") for p in value.split("/")):
        raise ValueError(f"unsafe manifest path: {value!r}")
    return path


def inventory(root):
    """Return metadata and bounded source bytes without following any symlink."""
    entries, contents, errors = {}, {}, []
    total = 0
    count = 0

    def visit(fd, prefix):
        nonlocal total, count
        with os.scandir(fd) as scanner:
            names = []
            for entry in scanner:
                if count + len(names) >= MAX_ENTRIES:
                    raise ValueError("workspace entry limit exceeded")
                names.append(entry.name)
            names.sort()
        for name in names:
            count += 1
            if count > MAX_ENTRIES:
                raise ValueError("workspace entry limit exceeded")
            path = f"{prefix}/{name}" if prefix else name
            meta = os.stat(name, dir_fd=fd, follow_symlinks=False)
            item = {"mode": stat.S_IMODE(meta.st_mode)}
            entries[path] = item
            if stat.S_ISLNK(meta.st_mode):
                item.update(kind="symlink", target=os.readlink(name, dir_fd=fd))
            elif stat.S_ISDIR(meta.st_mode):
                item["kind"] = "directory"
                child = os.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
                try:
                    visit(child, path)
                finally:
                    os.close(child)
            elif stat.S_ISREG(meta.st_mode):
                item.update(kind="file", size=meta.st_size, links=meta.st_nlink)
                if meta.st_size > MAX_FILE_BYTES or total + meta.st_size > MAX_TOTAL_BYTES:
                    errors.append({"path": path, "kind": "content_limit"})
                    continue
                child = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=fd)
                try:
                    opened = os.fstat(child)
                    if not stat.S_ISREG(opened.st_mode) or (opened.st_dev, opened.st_ino) != (meta.st_dev, meta.st_ino):
                        raise ValueError(f"file changed during inventory: {path}")
                    chunks, length = [], 0
                    while True:
                        block = os.read(child, min(65536, MAX_FILE_BYTES + 1 - length))
                        if not block:
                            break
                        chunks.append(block)
                        length += len(block)
                        if length > MAX_FILE_BYTES or total + length > MAX_TOTAL_BYTES:
                            raise ValueError(f"content grew beyond limit: {path}")
                    after = os.fstat(child)
                    if (after.st_size, after.st_mtime_ns, after.st_ctime_ns) != (opened.st_size, opened.st_mtime_ns, opened.st_ctime_ns):
                        raise ValueError(f"file changed during read: {path}")
                finally:
                    os.close(child)
                data = b"".join(chunks)
                total += len(data)
                item["sha256"] = digest(data)
                if Path(path).suffix in {".py", ".js", ".rs", ".lean", ".md"}:
                    contents[path] = data
            else:
                item["kind"] = "special"
    try:
        root_fd = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        try:
            visit(root_fd, "")
        finally:
            os.close(root_fd)
    except (OSError, ValueError) as error:
        errors.append({"kind": "inventory_error", "detail": str(error)})
    return entries, contents, errors


def generated_extra(path):
    parts = PurePosixPath(path).parts
    return "__pycache__" in parts and (parts[-1] == "__pycache__" or path.endswith(".pyc"))


def source_flags(path, data):
    try:
        lines = data.decode("utf-8").splitlines()
    except UnicodeDecodeError:
        return [{"path": path, "kind": "non_utf8_source"}]
    findings = []
    for number, line in enumerate(lines, 1):
        for label, pattern in PATTERNS:
            if pattern.search(line):
                findings.append({"path": path, "line": number, "kind": label})
    return findings


def audit_run(directory, task, corpus):
    result = json.loads((directory / "result.json").read_text())
    actual, source, errors = inventory(directory / "workspace")
    baseline, _, baseline_errors = inventory(corpus / safe_relative(task["fixture"]))
    editable = set(task["editable"])
    expected = task["artifact_sha256"]
    for path in set(expected) | editable | set(task["immutable"]):
        safe_relative(path)
    issues = list(errors)
    if baseline_errors:
        issues.append({"kind": "baseline_inventory_error", "details": baseline_errors})
    if result.get("run_id") != directory.name or result.get("task_id") != task["id"]:
        issues.append({"kind": "result_identity_mismatch"})
    for path, expected_hash in expected.items():
        if baseline.get(path, {}).get("sha256") != expected_hash:
            issues.append({"path": path, "kind": "fixture_manifest_mismatch"})
    protected = sorted(set(expected) - editable)
    changed, missing, protected_changes, mode_changes = [], [], [], []
    for path, expected_hash in expected.items():
        item = actual.get(path)
        if item is None:
            missing.append(path)
        elif item.get("sha256") != expected_hash:
            change = {"path": path, "kind": item["kind"], "before_sha256": expected_hash,
                      "after_sha256": item.get("sha256")}
            (changed if path in editable else protected_changes).append(change)
        if item and path in baseline and item["mode"] != baseline[path]["mode"]:
            mode_changes.append({"path": path, "before": baseline[path]["mode"], "after": item["mode"]})
    extras = [{"path": path, **item, "classification": "generated_cache" if generated_extra(path) else "review"}
              for path, item in actual.items() if path not in baseline]
    links = [{"path": path, **item} for path, item in actual.items() if item["kind"] == "symlink"]
    specials = [path for path, item in actual.items() if item["kind"] == "special"]
    hardlinks = [path for path, item in actual.items() if item.get("links", 1) > 1]
    flags = [flag for path in sorted(editable) if path in source for flag in source_flags(path, source[path])]
    checker_hashes = result.get("checker", {}).get("candidate_sha256", {})
    mismatches = [path for path, checked in checker_hashes.items() if actual.get(path, {}).get("sha256") != checked]
    for label, values in [("missing_files", missing), ("protected_changes", protected_changes),
                          ("symlinks", links), ("special_files", specials), ("hardlinks", hardlinks),
                          ("mode_changes", mode_changes), ("checker_artifact_mismatch", mismatches)]:
        if values:
            issues.append({"kind": label, "paths": [x["path"] if isinstance(x, dict) else x for x in values]})
    fingerprint = digest(json.dumps(actual, sort_keys=True, separators=(",", ":")).encode())
    return {"run_id": directory.name, "task_id": task["id"], "split": task["split"],
            "engine": result.get("engine"), "track": result.get("track"), "repetition": result.get("repetition"),
            "reported_success": result.get("success"), "checker_passed": result.get("checker", {}).get("passed"),
            "checker_failures": result.get("checker", {}).get("failures", []),
            "snapshot_sha256": fingerprint, "allowed_source_changes": sorted(changed, key=lambda x: x["path"]),
            "protected_files_checked": protected, "protected_changes": protected_changes,
            "missing_files": missing, "extras": extras, "symlinks": links, "special_files": specials,
            "hardlinks": hardlinks, "mode_changes": mode_changes, "issues": issues, "source_review_flags": flags,
            "manual_review": {"status": "not_reviewed"}}


def audit_suite(directory, corpus, previous=None):
    manifest_path = corpus / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    tasks = {task["id"]: task for task in manifest["tasks"]}
    old = {run["run_id"]: run for run in (previous or {}).get("runs", [])}
    runs, pending, errors = [], [], []
    for child in sorted(directory.iterdir()):
        if not child.is_dir():
            continue
        if child.is_symlink():
            errors.append({"run_id": child.name, "kind": "symlink_run_directory"})
            continue
        result_path = child / "result.json"
        if not result_path.exists():
            pending.append(child.name)
            continue
        try:
            result = json.loads(result_path.read_text())
            task = tasks[result["task_id"]]
            run = audit_run(child, task, corpus)
            former = old.get(child.name, {})
            if former.get("snapshot_sha256") == run["snapshot_sha256"]:
                run["manual_review"] = former.get("manual_review", {"status": "not_reviewed"})
            runs.append(run)
        except (OSError, ValueError, KeyError) as error:
            errors.append({"run_id": child.name, "kind": "run_read_error", "detail": str(error)})
    manifest_hash = digest(manifest_path.read_bytes())
    expected_runs, cohort_complete = None, None
    plan_path = directory / "plan.json"
    if plan_path.exists():
        plan = json.loads(plan_path.read_text())
        if plan.get("manifest_sha256") != manifest_hash:
            errors.append({"kind": "plan_manifest_mismatch"})
        if all(key in plan for key in ("tasks", "tracks", "engines", "repetitions")):
            expected = set(itertools.product(plan["tasks"], plan["tracks"], plan["engines"], range(plan["repetitions"])))
            actual = [(run["task_id"], run["track"], run["engine"], run["repetition"]) for run in runs]
            expected_runs = len(expected)
            if len(set(actual)) != len(actual):
                errors.append({"kind": "duplicate_planned_run"})
            if set(actual) - expected:
                errors.append({"kind": "unplanned_runs", "cells": sorted(set(actual) - expected)})
            cohort_complete = set(actual) == expected and len(actual) == expected_runs and not errors
    return {"schema_version": 1, "artifact_directory": str(directory), "manifest_sha256": manifest_hash,
            "audit_program_sha256": digest(Path(__file__).read_bytes()),
            "scope": "Post-run files only; no candidate execution, model-output review, or task score changes.",
            "limits": {"max_entries": MAX_ENTRIES, "max_file_bytes": MAX_FILE_BYTES, "max_total_bytes": MAX_TOTAL_BYTES},
            "limitations": ["Requires quiescent completed workspaces; does not prove historical isolation or detect reverted edits.",
                "Static pattern matches are review hints, not evidence of checker bypass; absence of matches proves no source-level property.",
                "Manual review is separate and bound to an exact file snapshot; correctness still depends on the independent checker and its coverage."],
            "completed_runs": len(runs), "expected_runs": expected_runs, "cohort_complete": cohort_complete,
            "pending_directories": pending, "errors": errors,
            "runs_with_inventory_issues": sum(bool(run["issues"]) for run in runs),
            "runs_with_source_flags": sum(bool(run["source_review_flags"]) for run in runs),
            "manual_reviewed_runs": sum(run["manual_review"].get("status") == "reviewed" for run in runs), "runs": runs}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--corpus", type=Path, default=ROOT / "eval/corpus")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--previous", type=Path, help="retain manual reviews only when the entire snapshot matches")
    args = parser.parse_args()
    previous = json.loads(args.previous.read_text()) if args.previous else None
    report = audit_suite(args.directory, args.corpus, previous)
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n")
    print(json.dumps({key: report[key] for key in ["completed_runs", "runs_with_inventory_issues", "runs_with_source_flags", "manual_reviewed_runs", "errors"]}))


if __name__ == "__main__":
    main()
