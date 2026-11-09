"""Kill the real executable at persistence boundaries; inspect effects independently."""
import json
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from integration import response

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / ".lake/build/bin/harness"

SHIM = r'''
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>
static int armed = 0, crash_on_sync = 0;
static int journal(int fd) {
    char source[64], target[4096];
    snprintf(source,sizeof(source),"/proc/self/fd/%d",fd);
    ssize_t n=readlink(source,target,sizeof(target)-1);
    if(n<0) return 0;
    target[n]=0;
    return n>=14 && strcmp(target+n-14,"/journal.jsonl")==0;
}
ssize_t write(int fd,const void *data,size_t size) {
    static ssize_t (*real_write)(int,const void*,size_t);
    if(!real_write) real_write=dlsym(RTLD_NEXT,"write");
    const char *mode=getenv("HARNESS_TEST_CRASH");
    if(mode && journal(fd)) {
        int intent=memmem(data,size,"\"kind\":\"intent\"",15)!=NULL;
        int tool=memmem(data,size,"\"kind\":\"tool\"",13)!=NULL;
        int completion=memmem(data,size,"\"kind\":\"completion\"",19)!=NULL;
        int resolution=memmem(data,size,"\"kind\":\"resolution\"",19)!=NULL;
        if(resolution) {
            if(!strcmp(mode,"before_resolution")) {errno=ENOSPC;return -1;}
            if(!strcmp(mode,"after_resolution")) crash_on_sync=1;
        }
        if(intent && tool) {
            if(!strcmp(mode,"before_intent")) {errno=ENOSPC;return -1;}
            armed=1;
            if(!strcmp(mode,"after_intent")) crash_on_sync=1;
        }
        if(armed && completion) {
            if(!strcmp(mode,"after_effect")) _exit(86);
            if(!strcmp(mode,"after_completion")) crash_on_sync=1;
        }
    }
    return real_write(fd,data,size);
}
int fsync(int fd) {
    static int (*real_fsync)(int);
    if(!real_fsync) real_fsync=dlsym(RTLD_NEXT,"fsync");
    const char *mode=getenv("HARNESS_TEST_CRASH");
    struct stat info;
    if(mode && !journal(fd) && fstat(fd,&info)==0 &&
       ((!strcmp(mode,"reconcile_file_sync") && S_ISREG(info.st_mode)) ||
        (!strcmp(mode,"reconcile_directory_sync") && S_ISDIR(info.st_mode)))) {
        errno=EIO;return -1;
    }
    int result=real_fsync(fd);
    if(result==0 && crash_on_sync && journal(fd)) _exit(86);
    return result;
}
'''


class CrashRecovery(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        source = Path(cls.temp.name) / "crash.c"
        source.write_text(SHIM)
        cls.shim = source.with_suffix(".so")
        subprocess.run(["cc", "-shared", "-fPIC", str(source), "-o", str(cls.shim), "-ldl"], check=True)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def scenario(self, mode):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        ws = root / "workspace"
        ws.mkdir()
        config = root / "config.json"
        config.write_text(json.dumps({"model": "scripted", "commands": "allow"}))
        script = root / "script.json"
        script.write_text(json.dumps([
            response([("append-once", "process", {"argv": ["/bin/sh", "-c", "printf x >> counter"]})]),
            response(text="done")]))
        session = root / "session"
        result = subprocess.run([str(BIN), "run", "--workspace", str(ws), "--config", str(config),
                                 "--task", "append once", "--script", str(script), "--session", str(session)],
                                env={**os.environ, "LD_PRELOAD": str(self.shim), "HARNESS_TEST_CRASH": mode},
                                text=True, capture_output=True, timeout=15)
        self.assertEqual(result.returncode, 2 if mode == "before_intent" else 86,
                         result.stderr + result.stdout)
        return session, ws / "counter"

    def resume(self, session):
        return subprocess.run([str(BIN), "resume", str(session)], text=True, capture_output=True, timeout=15)

    def inspect(self, session):
        result = subprocess.run([str(BIN), "inspect", str(session)], text=True, capture_output=True, check=True)
        return json.loads(result.stdout)

    def resolve(self, session, status="completed", expected=0):
        operation = self.inspect(session)["recoverableOperation"]
        args = [str(BIN), "resolve", str(session), "--operation", str(operation),
                "--status", status, "--note", "Operator inspected effects and settled original resources",
                "--resources-settled"]
        if status == "completed":
            args += ["--exit-code", "0"]
        result = subprocess.run(args, text=True, capture_output=True, timeout=15)
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        return operation

    def edit_scenario(self, mode):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        workspace = root / "workspace"
        workspace.mkdir()
        target = workspace / "file.txt"
        target.write_text("before\n")
        config = root / "config.json"
        config.write_text(json.dumps({"model": "scripted"}))
        script = root / "script.json"
        script.write_text(json.dumps([
            response([("edit-once", "edit", {"path": "file.txt", "old": "before", "new": "after",
                "expectedSha256": hashlib.sha256(b"before\n").hexdigest()})]), response(text="done")]))
        session = root / "session"
        result = subprocess.run([str(BIN), "run", "--workspace", str(workspace), "--config", str(config),
                                 "--task", "edit once", "--script", str(script), "--session", str(session)],
                                env={**os.environ, "LD_PRELOAD": str(self.shim), "HARNESS_TEST_CRASH": mode},
                                text=True, capture_output=True, timeout=15)
        self.assertEqual(result.returncode, 86, result.stderr + result.stdout)
        return session, target

    def test_failed_intent_write_does_not_dispatch(self):
        session, counter = self.scenario("before_intent")
        self.assertFalse(counter.exists())
        self.assertFalse(self.inspect(session)["pending"])
        self.assertEqual(self.resume(session).returncode, 0)
        self.assertEqual(counter.read_bytes(), b"x")

    def test_durable_intent_crash_is_uncertain_without_dispatch(self):
        session, counter = self.scenario("after_intent")
        self.assertFalse(counter.exists())
        self.assertTrue(self.inspect(session)["pending"])
        self.assertEqual(self.resume(session).returncode, 2)
        self.assertFalse(counter.exists())

    def test_effect_without_completion_is_never_repeated(self):
        session, counter = self.scenario("after_effect")
        self.assertEqual(counter.read_bytes(), b"x")
        self.assertTrue(self.inspect(session)["pending"])
        self.assertEqual(self.resume(session).returncode, 2)
        self.assertEqual(counter.read_bytes(), b"x")

    def test_durable_completion_replays_without_repeating_effect(self):
        session, counter = self.scenario("after_completion")
        self.assertEqual(counter.read_bytes(), b"x")
        self.assertFalse(self.inspect(session)["pending"])
        self.assertEqual(self.resume(session).returncode, 0)
        self.assertEqual(counter.read_bytes(), b"x")
        self.assertEqual(self.inspect(session)["state"]["toolDispatches"], 1)

    def test_postimage_reconciliation_resumes_without_another_edit(self):
        session, target = self.edit_scenario("after_effect")
        self.assertEqual(target.read_bytes(), b"after\n")
        pending = self.inspect(session)
        self.assertTrue(pending["pending"])
        self.assertEqual(pending["editWitness"]["postimage"], hashlib.sha256(b"after\n").hexdigest())
        self.assertEqual(self.resume(session).returncode, 0)
        self.assertEqual(target.read_bytes(), b"after\n")
        final = self.inspect(session)
        self.assertEqual(final["state"]["toolDispatches"], 1)
        self.assertIsNone(final["recoverableOperation"])
        records = [json.loads(line)["record"] for line in (session / "journal.jsonl").read_text().splitlines()]
        resolutions = [r for r in records if r["kind"] == "resolution"]
        self.assertEqual(len(resolutions), 1)
        self.assertEqual(resolutions[0]["source"], "application_evidence")
        self.assertEqual(sum(r["kind"] == "intent" and r["action"]["kind"] == "tool" for r in records), 1)

    def test_preimage_and_conflict_refuse_automatic_edit_replay(self):
        session, target = self.edit_scenario("after_intent")
        saved = (session / "journal.jsonl").read_bytes()
        self.assertEqual(target.read_bytes(), b"before\n")
        self.assertEqual(self.resume(session).returncode, 2)
        self.assertEqual(target.read_bytes(), b"before\n")
        target.write_text("external edit\n")
        self.assertEqual(self.resume(session).returncode, 2)
        self.assertEqual(target.read_bytes(), b"external edit\n")
        self.assertEqual((session / "journal.jsonl").read_bytes(), saved)

    def test_operator_completion_is_recorded_once_and_does_not_rerun(self):
        session, counter = self.scenario("after_effect")
        pending_id = self.inspect(session)["recoverableOperation"]
        before = (session / "journal.jsonl").read_bytes()
        missing_assertion = subprocess.run([str(BIN), "resolve", str(session), "--operation", str(pending_id),
            "--status", "completed", "--exit-code", "0", "--note", "--resources-settled"],
            text=True, capture_output=True, timeout=15)
        self.assertEqual(missing_assertion.returncode, 2)
        self.assertEqual((session / "journal.jsonl").read_bytes(), before)
        operation = self.resolve(session)
        repeated = subprocess.run([str(BIN), "resolve", str(session), "--operation", str(operation),
            "--status", "completed", "--exit-code", "0", "--note", "duplicate",
            "--resources-settled"], text=True, capture_output=True, timeout=15)
        self.assertEqual(repeated.returncode, 2)
        self.assertEqual(counter.read_bytes(), b"x")
        self.assertEqual(self.resume(session).returncode, 0)
        self.assertEqual(counter.read_bytes(), b"x")
        loaded = self.inspect(session)
        self.assertEqual(loaded["state"]["toolDispatches"], 1)
        self.assertIn("not independently verified", json.dumps(loaded))

    def test_operator_can_abandon_unknown_outcome_without_dispatch(self):
        session, counter = self.scenario("after_intent")
        self.resolve(session, "abandoned")
        self.assertEqual(self.resume(session).returncode, 0)
        self.assertFalse(counter.exists())
        self.assertEqual(self.inspect(session)["state"]["toolDispatches"], 1)

    def test_resolution_storage_boundary_is_replayable(self):
        for mode in ("before_resolution", "after_resolution"):
            with self.subTest(mode=mode):
                session, target = self.edit_scenario("after_effect")
                before = (session / "journal.jsonl").read_bytes()
                result = subprocess.run([str(BIN), "resume", str(session)], text=True,
                    capture_output=True, timeout=15,
                    env={**os.environ, "LD_PRELOAD": str(self.shim), "HARNESS_TEST_CRASH": mode})
                self.assertEqual(result.returncode, 2 if mode == "before_resolution" else 86,
                                 result.stdout + result.stderr)
                if mode == "before_resolution":
                    self.assertEqual((session / "journal.jsonl").read_bytes(), before)
                    self.assertTrue(self.inspect(session)["pending"])
                else:
                    self.assertFalse(self.inspect(session)["pending"])
                    self.assertFalse(self.inspect(session)["terminal"])
                self.assertEqual(self.resume(session).returncode, 0)
                self.assertEqual(target.read_bytes(), b"after\n")
                records = [json.loads(line)["record"] for line in (session / "journal.jsonl").read_text().splitlines()]
                self.assertEqual(sum(r["kind"] == "resolution" for r in records), 1)
                self.assertEqual(self.inspect(session)["state"]["toolDispatches"], 1)

    def test_reconciliation_requires_file_and_directory_durability(self):
        for mode in ("reconcile_file_sync", "reconcile_directory_sync"):
            with self.subTest(mode=mode):
                session, target = self.edit_scenario("after_effect")
                before = (session / "journal.jsonl").read_bytes()
                result = subprocess.run([str(BIN), "resume", str(session)], text=True,
                    capture_output=True, timeout=15,
                    env={**os.environ, "LD_PRELOAD": str(self.shim), "HARNESS_TEST_CRASH": mode})
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertEqual((session / "journal.jsonl").read_bytes(), before)
                self.assertTrue(self.inspect(session)["pending"])
                self.assertEqual(target.read_bytes(), b"after\n")
                self.assertEqual(self.resume(session).returncode, 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
