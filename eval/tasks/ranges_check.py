#!/usr/bin/env python3
"""Independent development-smoke checker; never copy this into the agent workspace.

This is a self-authored development task, not a held-out benchmark. It compares
black-box outputs outside the candidate process, and checks the visible fixtures
were not modified. It does not establish hostile-code sandboxing.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

FIXTURE = Path(__file__).resolve().parent / "ranges"
VALID = [
    ("", []),
    (" \t\n ", []),
    ("1", [1]),
    (" 7 ", [7]),
    ("3,1,2", [1, 2, 3]),
    ("1-3", [1, 2, 3]),
    ("5-5", [5]),
    ("2,1-3,2", [1, 2, 3]),
    ("001,003-005", [1, 3, 4, 5]),
    ("\t2 - 4,\n1 ", [1, 2, 3, 4]),
    ("2,02,0002", [2]),
    ("9,7-8,4-5,4", [4, 5, 7, 8, 9]),
    ("10-12,8-10", [8, 9, 10, 11, 12]),
    ("20,19-20,18", [18, 19, 20]),
]
INVALID = [
    ",", "1,", ",1", "1,,2", "1, ,2", "0", "000", "0-2", "2-0",
    "3-1", "01-00", "-1", "+1", "1--2", "1-2-3", "1-", "-",
    "one", "1.0", "1e2", "1_0", "1 2", "1;+2", "\u0661", "\uff11",
    "1-\u0662", "1,+2", "1-2,0", "1-2,4-3",
]

# Expected answers never enter the candidate process. -I -S avoids importing
# candidate sitecustomize files; only ranges.py is copied into the temporary evaluation directory.
WORKER = r'''
import importlib.util, json, sys
spec = importlib.util.spec_from_file_location("candidate_ranges", sys.argv[1])
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
answers = []
for text in json.load(sys.stdin):
    try:
        value = module.parse_ranges(text)
        if type(value) is not list or any(type(n) is not int for n in value):
            answers.append({"kind": "wrong_type"})
        else:
            answers.append({"kind": "value", "value": value})
    except ValueError:
        answers.append({"kind": "value_error"})
    except Exception as error:
        answers.append({"kind": "exception", "type": type(error).__name__})
print(json.dumps(answers, separators=(",", ":")))
'''


def evaluate(workspace: Path) -> dict:
    workspace = workspace.resolve()
    failures = []
    for filename in ["README.md", "test_ranges.py"]:
        candidate = workspace / filename
        if not candidate.is_file() or candidate.is_symlink() or candidate.read_bytes() != (FIXTURE / filename).read_bytes():
            failures.append({"kind": "fixture_modified", "file": filename})
    source = workspace / "ranges.py"
    if not source.is_file() or source.is_symlink():
        return {"passed": False, "failures": failures + [{"kind": "missing_or_symlinked_source"}]}
    code = source.read_bytes()
    if len(code) > 128 * 1024:
        return {"passed": False, "failures": failures + [{"kind": "oversized_source"}]}
    cases = [text for text, _ in VALID] + INVALID
    expected = [{"kind": "value", "value": value} for _, value in VALID] + [
        {"kind": "value_error"} for _ in INVALID
    ]
    with tempfile.TemporaryDirectory(prefix="ranges-independent-check-") as directory:
        copied = Path(directory) / "ranges.py"
        copied.write_bytes(code)
        try:
            run = subprocess.run(
                [sys.executable, "-I", "-S", "-c", WORKER, str(copied)],
                cwd=directory, input=json.dumps(cases), text=True,
                capture_output=True, timeout=10,
            )
        except subprocess.TimeoutExpired:
            return {"passed": False, "failures": failures + [{"kind": "timeout"}]}
    try:
        actual = json.loads(run.stdout) if run.returncode == 0 else None
    except json.JSONDecodeError:
        actual = None
    if not isinstance(actual, list) or len(actual) != len(expected):
        failures.append({"kind": "candidate_process_failure", "exit_code": run.returncode})
    else:
        for index, (result, wanted) in enumerate(zip(actual, expected)):
            if result != wanted:
                failures.append({"kind": "case_failure", "case": index})
    return {"passed": not failures, "case_count": len(expected),
            "fixture_integrity_checks": 2, "source_sha256": hashlib.sha256(code).hexdigest(),
            "failures": failures, "label": "self-authored development smoke; not held-out"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    args = parser.parse_args()
    result = evaluate(args.workspace)
    print(json.dumps(result, indent=2))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
