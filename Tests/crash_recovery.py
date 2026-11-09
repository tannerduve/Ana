"""Kill the real executable at persistence boundaries; inspect effects independently."""
import json
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


if __name__ == "__main__":
    unittest.main(verbosity=2)
