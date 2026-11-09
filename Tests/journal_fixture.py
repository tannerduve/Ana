"""Test utility: use compiled journal IO when constructing valid replay fixtures."""
import json
from pathlib import Path
import subprocess

BIN = Path(__file__).resolve().parents[1] / ".lake/build/bin/runtime_contracts"


def request(value):
    result = subprocess.run([str(BIN)], input=json.dumps(value), text=True,
                            capture_output=True, check=True, timeout=30)
    observed = json.loads(result.stdout)
    if observed["status"] != "ok":
        raise ValueError(observed.get("error", observed))
    return observed


def journal_append(path, record):
    return request({"op": "journalAppend", "path": str(path), "record": record})


def journal_read(path):
    return request({"op": "journalRead", "path": str(path)})
