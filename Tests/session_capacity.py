"""Optional capacity measurement of a real CLI session, without model calls.

A loopback provider preserves a large synthetic opaque block, fills the artifact
quota, reads a diagnostic beyond the display prefix, then advances until journal
admission refuses another operation. Inspect/replay and an independent record
count verify the retained session. This is capacity evidence, not task quality.
"""
import argparse
import hashlib
import http.server
import json
from pathlib import Path
import shutil
import subprocess
import threading
import time

from provider_streaming import event

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / ".lake/build/bin/harness"
MIB = 1024 * 1024
TAIL = "CAPACITY-DIAGNOSTIC: use addition\n"


def call(identifier, name, args):
    return {"type": "tool_use", "id": identifier, "name": name, "input": args}


def wire(blocks):
    chunks = [event("message_start", message={"type": "message", "role": "assistant",
        "id": "capacity-fixture", "content": [], "stop_reason": None,
        "usage": {"input_tokens": 1, "output_tokens": 0}})]
    for index, block in enumerate(blocks):
        chunks += [event("content_block_start", index=index, content_block=block),
                   event("content_block_stop", index=index)]
    chunks += [event("message_delta", delta={"stop_reason": "tool_use"}, usage={"output_tokens": 1}),
               event("message_stop")]
    return b"".join(chunks)


class Provider(http.server.BaseHTTPRequestHandler):
    def log_message(self, *_):
        pass

    def do_POST(self):
        try:
            size = int(self.headers["Content-Length"])
            assert 0 < size < 2 * MIB
            request = json.loads(self.rfile.read(size))
            number = len(self.server.requests)
            self.server.requests.append({"bytes": size, "seconds": time.monotonic() - self.server.started})
            if number == 0:
                blocks = [{"type": "redacted_thinking", "data": "x" * MIB}]
                for index in range(4):
                    code = f"import os; os.write(1,b'x'*({16*MIB}-{len(TAIL)})); os.write(1,{TAIL.encode()!r})"
                    blocks.append(call(f"bulk-{index}", "process", {"argv": ["/usr/bin/python3", "-c", code]}))
            elif number == 1:
                catalog = request["messages"][0]["content"][0]["text"]
                refs = json.loads(catalog.split("\n", 1)[1])
                assert len(refs) == 4 and sum(ref["storedBytes"] for ref in refs) == 64 * MIB
                blocks = [call("retrieve-tail", "artifact", {"id": refs[-1]["id"],
                    "offset": 16 * MIB - len(TAIL), "length": 128})]
            elif number == 2:
                results = [block for message in request["messages"] for block in message["content"]
                           if block.get("type") == "tool_result" and block["tool_use_id"] == "retrieve-tail"]
                assert len(results) == 1 and not results[0].get("is_error", False)
                assert TAIL.strip() in json.loads(results[0]["content"])["text"]
                self.server.tail_read = True
                blocks = [call("repair", "create", {"path": "verified.txt", "content": TAIL})]
            elif number == 3:
                blocks = [call("quota-exhausted", "process", {"argv": ["/usr/bin/python3", "-c",
                    "import os; os.write(1,b'z'*1048576)"]})]
            else:
                blocks = [call(f"read-{number}", "read", {"path": "verified.txt"})]
            body = wire(blocks)
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        except Exception as error:
            self.server.errors.append(repr(error))
            self.send_error(500, "capacity fixture assertion failed")


def measured(output, name, arguments, timeout=1200):
    started = time.monotonic()
    with (output / f"{name}.stdout").open("w") as stdout, (output / f"{name}.stderr").open("w") as stderr:
        result = subprocess.run(["/usr/bin/time", "-f", "%M", "-o", str(output / f"{name}.rss"),
                                 str(BIN), *map(str, arguments)], stdout=stdout, stderr=stderr, timeout=timeout)
    return {"exit_code": result.returncode, "seconds": time.monotonic() - started,
            "peak_worker_rss_kib": int((output / f"{name}.rss").read_text().splitlines()[-1])}


def main():
    global BIN
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--binary", type=Path, default=BIN)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(mode=0o700, parents=True, exist_ok=False)
    driver = Path(__file__).read_bytes()
    (output / "session_capacity.py").write_bytes(driver)
    streaming_fixture = Path(__file__).with_name("provider_streaming.py").read_bytes()
    (output / "provider_streaming.py").write_bytes(streaming_fixture)
    # Pin the exact executable for run and offline replay even if another build
    # replaces the working tree's binary while this optional measurement runs.
    shutil.copy2(args.binary, output / "harness")
    BIN = output / "harness"
    workspace, session = output / "workspace", output / "session"
    workspace.mkdir()
    server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Provider)
    server.requests, server.errors, server.tail_read, server.started = [], [], False, time.monotonic()
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    config = {"model": "capacity-fixture", "workspace": str(workspace), "commands": "allow",
        "executionProfile": "bubblewrap", "compactionEnabled": False,
        "maxModelAttempts": 80, "maxToolCalls": 100, "maxContextBytes": 1300000,
        "maxRetries": 0,
        "maxToolOutputBytes": 16384, "maxElapsedMs": 1200000, "operationTimeoutMs": 30000,
        "maxArtifactBytes": 16 * MIB, "maxSessionArtifactBytes": 64 * MIB,
        "testEndpoint": f"http://127.0.0.1:{server.server_port}/messages"}
    config_path = output / "config.json"
    config_path.write_text(json.dumps(config))
    try:
        run = measured(output, "run", ["run", "--workspace", workspace, "--config", config_path,
            "--task", "Exercise bounded artifact retrieval and durable session capacity.", "--session", session, "--json"])
    finally:
        server.shutdown()
        server.server_close()
    assert not server.errors, server.errors
    assert server.tail_read and (workspace / "verified.txt").read_text() == TAIL
    assert run["exit_code"] != 0 and "64 MiB" in (output / "run.stderr").read_text()
    journal = session / "journal.jsonl"
    original = hashlib.sha256(journal.read_bytes()).hexdigest()
    inspection = measured(output, "inspect", ["inspect", session])
    replay = measured(output, "replay", ["replay", session])
    assert inspection["exit_code"] == replay["exit_code"] == 0
    observed = json.loads((output / "inspect.stdout").read_text())
    assert observed == json.loads((output / "replay.stdout").read_text())
    assert hashlib.sha256(journal.read_bytes()).hexdigest() == original
    state = observed["state"]
    frames = [json.loads(line) for line in journal.read_text().splitlines()]
    intents = [frame["record"] for frame in frames if frame["record"]["kind"] == "intent"]
    assert sum(record["action"]["kind"] == "model" for record in intents) == len(server.requests)
    assert not observed["terminal"] and not observed["interruptedStorage"]
    # Byte admission can refuse either an intent or its completion. Do not
    # assume the serialized frame sizes put every release at the same phase.
    # A completed effect whose completion does not fit must remain pending.
    completed_ids = {frame["record"]["id"] for frame in frames
                     if frame["record"]["kind"] == "completion"}
    unresolved = [record for record in intents if record["id"] not in completed_ids]
    assert len(unresolved) == int(observed["pending"])
    if unresolved:
        assert frames[-1]["record"] == unresolved[0]
        assert unresolved[0]["id"] == state["nextId"]
    assert len(server.requests) <= state["modelAttempts"] <= len(server.requests) + 1
    if state["modelAttempts"] > len(server.requests):
        assert not observed["pending"] and "model" in state["phase"]
    refs = state["artifacts"]
    assert sum(ref["storedBytes"] for ref in refs) == config["maxSessionArtifactBytes"]
    assert any(ref["storedBytes"] == 0 and ref["truncated"] for ref in refs)
    for ref in refs:
        blob = session / "artifacts" / (ref["id"] + ".blob")
        assert blob.stat().st_size == ref["storedBytes"]
        assert hashlib.sha256(blob.read_bytes()).hexdigest() == ref["sha256"]
    assert 60 * MIB < journal.stat().st_size <= 64 * MIB
    report = {"scope": "synthetic real CLI capacity; loopback provider, no paid calls or task-quality claim",
        "memory_measurement": "GNU time maximum per-process RSS of the command and waited-for children; not simultaneous process-tree memory",
        "driver_sha256": hashlib.sha256(driver).hexdigest(),
        "streaming_fixture_sha256": hashlib.sha256(streaming_fixture).hexdigest(),
        "binary_sha256": hashlib.sha256(BIN.read_bytes()).hexdigest(), "config": config,
        "run": run, "inspect": inspection, "replay": replay, "requests": server.requests,
        "model_requests": len(server.requests), "tool_dispatches": state["toolDispatches"],
        "reserved_model_attempts": state["modelAttempts"], "pending": observed["pending"],
        "terminal": observed["terminal"],
        "unresolved_intents": unresolved,
        "storage_boundary": "completion" if unresolved else "intent",
        "journal_frames": len(frames), "journal_bytes": journal.stat().st_size,
        "artifact_bytes": sum(ref["storedBytes"] for ref in refs), "artifact_count": len(refs),
        "beyond_display_retrieval": True, "zero_retained_quota_marker": True,
        "storage_refusal_preserved_replay": True, "no_unjournaled_model_dispatch": True}
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items() if key not in {"requests", "config"}}, indent=2))


if __name__ == "__main__":
    main()
