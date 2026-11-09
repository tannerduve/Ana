"""Optional storage-capacity measurement using the compiled journal adapter.

Creates a temporary 62 MiB journal through real appends, measures each worker,
then verifies a refused over-limit append leaves the valid prefix unchanged.
This exercises framing/IO, not semantic replay of a generated agent session.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / ".lake/build/bin/runtime_contracts"


def run(root, request):
    memory = root / "memory.txt"
    started = time.monotonic()
    result = subprocess.run(["/usr/bin/time", "-f", "%M", "-o", str(memory), str(BIN)],
                            input=json.dumps(request), text=True, capture_output=True, timeout=90)
    if result.returncode:
        raise RuntimeError(result.stderr)
    return json.loads(result.stdout), {"seconds": time.monotonic() - started,
                                      "worker_peak_rss_kib": int(memory.read_text())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="lean-harness-journal-scale-") as temporary:
        root = Path(temporary)
        # Check the measurement follows the allocated worker, not only its parent.
        subprocess.run(["/usr/bin/time", "-f", "%M", "-o", str(root / "probe.txt"),
                        "/usr/bin/python3", "-c", "x=bytearray(64*1024*1024); x[0]=1"], check=True)
        probe = int((root / "probe.txt").read_text())
        assert probe >= 64 * 1024, probe
        journal = root / "journal.jsonl"
        records, measurements = 31, []
        for sequence in range(records):
            observed, measurement = run(root, {"op": "journalAppend", "path": str(journal),
                "record": {"sequence": sequence, "payload": "x" * (2 * 1024 * 1024)}})
            assert observed["status"] == "ok", observed
            measurements.append({"record": sequence, "journal_bytes": journal.stat().st_size, **measurement})
        original = hashlib.sha256(journal.read_bytes()).hexdigest()
        summary, replay_measurement = run(root, {"op": "journalReadSummary", "path": str(journal)})
        assert summary["status"] == "ok" and summary["records"] == records and not summary["interrupted"], summary
        rejected, rejection_measurement = run(root, {"op": "journalAppend", "path": str(journal),
            "record": {"payload": "y" * (3 * 1024 * 1024)}})
        assert rejected["status"] == "failed" and "64 MiB" in rejected["error"], rejected
        assert hashlib.sha256(journal.read_bytes()).hexdigest() == original
        after, _ = run(root, {"op": "journalReadSummary", "path": str(journal)})
        assert after == summary
        report = {"binary_sha256": hashlib.sha256(BIN.read_bytes()).hexdigest(),
                  "record_count": records, "journal_bytes": journal.stat().st_size,
                  "measurement_probe_rss_kib": probe, "appends": measurements,
                  "read_validate": replay_measurement, "rejected_append": rejection_measurement,
                  "refused_append_preserved_prefix": True,
                  "scope": "actual journal adapter; synthetic records, not logical agent replay"}
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({key: value for key, value in report.items() if key != "appends"}, indent=2))


if __name__ == "__main__":
    main()
