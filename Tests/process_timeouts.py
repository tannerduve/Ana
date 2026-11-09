"""Settled sandbox deadlines, conservative refusals, and durable batch recovery.

The preload shim injects host-adapter faults only; it is not inherited by tools.
No credentials, network provider, Docker, or production test hooks are used.
"""
import fcntl
import hashlib
import http.server
import json
import os
from pathlib import Path
import subprocess
import tempfile
import threading
import time
import unittest

from integration import response

ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / ".lake/build/bin/runtime_contracts"
CLI = ROOT / ".lake/build/bin/harness"

SHIM = r'''
#define _GNU_SOURCE
#include <dirent.h>
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <sys/syscall.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
static int status_fd=-1, crash_sync=0, tool_intent_armed=0;
static const char *mode(void) { const char *m=getenv("TIMEOUT_FAULT");return m?m:""; }
static int has(const void *p,size_t n,const char *s) { return memmem(p,n,s,strlen(s))!=NULL; }
static void preparation_barrier(void) {
 static int used=0;if(used)return;used=1;
 const char *ready=getenv("TIMEOUT_PREP_READY"),*release=getenv("TIMEOUT_PREP_RELEASE");
 if(!ready || !release)abort();
 int fd=syscall(SYS_openat,AT_FDCWD,ready,O_WRONLY|O_CREAT|O_EXCL,0600);
 if(fd<0)abort();syscall(SYS_write,fd,"ready",5);syscall(SYS_close,fd);
 struct stat info;struct timespec pause={0,5000000};
 for(int i=0;i<1000;i++) {
  if(syscall(SYS_newfstatat,AT_FDCWD,release,&info,0)==0)return;
  nanosleep(&pause,NULL);
 }
 _exit(87);
}
static void provider_preparation(const char *path) {
 const char *expected=getenv("TIMEOUT_PREP_PATH");
 if(expected && !strcmp(mode(),"provider_preparation") && !strcmp(path,expected))preparation_barrier();
}
/* Pinned Lean/libuv issues statx through syscall(), bypassing libc stat.
   GCC forwarding preserves unrelated syscall arguments without decoding them. */
long syscall(long number,...) {
 void *arguments=__builtin_apply_args();
 static long (*real)(long,...);if(!real)real=dlsym(RTLD_NEXT,"syscall");
 if(number!=SYS_statx)__builtin_return(__builtin_apply((void(*)())real,arguments,128));
 va_list args;va_start(args,number);
 int dir=va_arg(args,int);const char *path=va_arg(args,const char*);
 int flags=va_arg(args,int);unsigned mask=va_arg(args,unsigned);void *info=va_arg(args,void*);va_end(args);
 long result=real(number,dir,path,flags,mask,info);int saved=errno;
 provider_preparation(path);errno=saved;return result;
}
int __xstat(int version,const char *path,struct stat *info) {
 static int (*real)(int,const char*,struct stat*);if(!real)real=dlsym(RTLD_NEXT,"__xstat");
 int result=real(version,path,info);int saved=errno;provider_preparation(path);errno=saved;return result;
}
int __xstat64(int version,const char *path,struct stat64 *info) {
 static int (*real)(int,const char*,struct stat64*);if(!real)real=dlsym(RTLD_NEXT,"__xstat64");
 int result=real(version,path,info);int saved=errno;provider_preparation(path);errno=saved;return result;
}
static int path_has(int fd,const char *part) {
 char path[64],target[4096];snprintf(path,sizeof(path),"/proc/self/fd/%d",fd);
 ssize_t n=readlink(path,target,sizeof(target)-1);if(n<0)return 0;target[n]=0;return strstr(target,part)!=NULL;
}
ssize_t read(int fd,void *data,size_t size) {
 static ssize_t (*real)(int,void*,size_t);if(!real)real=dlsym(RTLD_NEXT,"read");
 if(fd==status_fd && !strcmp(mode(),"status_open")) {errno=EAGAIN;return -1;}
 ssize_t n=real(fd,data,size);
 if(n>0 && has(data,n,"child-pid")) {
  status_fd=fd;
  const char *replacement=NULL;
  if(!strcmp(mode(),"status_missing"))return 0;
  if(!strcmp(mode(),"status_malformed"))replacement="{broken}\n";
  if(!strcmp(mode(),"status_duplicate"))replacement="{\"child-pid\":1}\n{\"child-pid\":2}\n";
  if(!strcmp(mode(),"status_reordered"))replacement="{\"exit-code\":0}\n{\"child-pid\":1}\n";
  if(replacement) {size_t k=strlen(replacement);if(k>size)abort();memcpy(data,replacement,k);return k;}
  if(!strcmp(mode(),"cancel_at_status") || !strcmp(mode(),"cancel_global")) {
   const char *path=getenv("TIMEOUT_CANCEL_PATH");
   int out=syscall(SYS_openat,AT_FDCWD,path,O_WRONLY|O_CREAT,0600);
   if(out>=0) {syscall(SYS_write,out,"cancel",6);syscall(SYS_close,out);}
  }
  if(!strcmp(mode(),"status_global") || !strcmp(mode(),"cancel_global"))preparation_barrier();
 }
 return n;
}
ssize_t readlinkat(int fd,const char *path,char *data,size_t size) {
 static ssize_t (*real)(int,const char*,char*,size_t);if(!real)real=dlsym(RTLD_NEXT,"readlinkat");
 if(!strcmp(mode(),"proc_mismatch") && !strcmp(path,"self")) {if(size<1)abort();data[0]='0';return 1;}
 ssize_t result=real(fd,path,data,size);
 if((!strcmp(mode(),"tool_preparation") || (!strcmp(mode(),"cli_preparation") && tool_intent_armed)) && !strcmp(path,"self"))preparation_barrier();
 return result;
}
DIR *opendir(const char *path) {
 static DIR *(*real)(const char*);if(!real)real=dlsym(RTLD_NEXT,"opendir");
 if(!strcmp(mode(),"scan_failure") && !strcmp(path,"/proc")) {errno=EACCES;return NULL;}
 return real(path);
}
pid_t waitpid(pid_t pid,int *status,int options) {
 static pid_t (*real)(pid_t,int*,int);if(!real)real=dlsym(RTLD_NEXT,"waitpid");
 pid_t result=real(pid,status,options);
 if(result>0 && !strcmp(mode(),"reap_failure")) {errno=ECHILD;return -1;}
 return result;
}
int waitid(idtype_t type,id_t pid,siginfo_t *info,int options) {
 static int (*real)(idtype_t,id_t,siginfo_t*,int);if(!real)real=dlsym(RTLD_NEXT,"waitid");
 int result=real(type,pid,info,options);
 if(result==0 && !strcmp(mode(),"cleanup_deadline"))memset(info,0,sizeof(*info));
 return result;
}
ssize_t write(int fd,const void *data,size_t size) {
 static ssize_t (*real)(int,const void*,size_t);if(!real)real=dlsym(RTLD_NEXT,"write");
 if(!strcmp(mode(),"artifact_failure") && path_has(fd,"/artifacts/")) {errno=ENOSPC;return -1;}
 if(path_has(fd,"/journal.jsonl") && has(data,size,"\"kind\":\"intent\"") && has(data,size,"\"kind\":\"tool\""))tool_intent_armed=1;
 if(path_has(fd,"/journal.jsonl") && has(data,size,"\"kind\":\"completion\"") && has(data,size,"\"timedOut\":")) {
  if(!strcmp(mode(),"before_completion"))_exit(86);
  if(!strcmp(mode(),"after_completion"))crash_sync=1;
 }
 return real(fd,data,size);
}
int fsync(int fd) {
 static int (*real)(int);if(!real)real=dlsym(RTLD_NEXT,"fsync");
 int result=real(fd);
 if(result==0 && crash_sync && path_has(fd,"/journal.jsonl"))_exit(86);
 return result;
}
'''

SLEEP = "import time; print('partial output',flush=True); open('effect','a').write('x'); time.sleep(30)"
DETACHED = """import fcntl,os,signal,time
reader,writer=os.pipe()
if os.fork()==0:
 os.close(reader); os.setsid(); signal.signal(signal.SIGTERM,signal.SIG_IGN)
 lease=os.open('/workspace/lease',os.O_RDWR|os.O_CREAT,0o600)
 fcntl.flock(lease,fcntl.LOCK_EX)
 null=os.open('/dev/null',os.O_RDWR)
 for fd in (0,1,2): os.dup2(null,fd)
 os.write(writer,b'x'); os.close(writer)
 while True: time.sleep(1)
os.close(writer)
assert os.read(reader,1)==b'x'
print('detached child ready',flush=True)
time.sleep(30)
"""


class ProcessTimeouts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.compiler = tempfile.TemporaryDirectory(prefix="harness-timeout-shim-")
        source = Path(cls.compiler.name) / "fault.c"
        source.write_text(SHIM)
        cls.shim = source.with_suffix(".so")
        subprocess.run(["cc", "-shared", "-fPIC", str(source), "-o", str(cls.shim), "-ldl"], check=True)

    @classmethod
    def tearDownClass(cls):
        cls.compiler.cleanup()

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="harness-timeouts-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.workspace = self.root / "workspace"
        self.workspace.mkdir()
        self.session = self.root / "session"
        self.session.mkdir()

    def env(self, fault=None):
        env = {key: os.environ[key] for key in ["PATH", "HOME", "LANG"] if key in os.environ}
        if fault:
            env.update(LD_PRELOAD=str(self.shim), TIMEOUT_FAULT=fault,
                       TIMEOUT_CANCEL_PATH=str(self.session / "cancel"))
        return env

    def tool_request(self, code=SLEEP, **options):
        return {"op": "tool", "workspace": str(self.workspace), "timeoutMs": 800,
                   "localDeadline": True, "executionProfile": "bubblewrap",
                   "artifactDir": str(self.session / "artifacts"), "cancelPath": str(self.session / "cancel"),
                   "call": {"name": "process", "args": {"argv": ["/usr/bin/python3", "-c", code]}}, **options}

    def tool(self, code=SLEEP, fault=None, **options):
        request = self.tool_request(code, **options)
        result = subprocess.run([str(DRIVER)], input=json.dumps(request) + "\n", text=True,
                                capture_output=True, env=self.env(fault), timeout=8)
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        return json.loads(result.stdout)

    def blocked_request(self, request, fault, budget_ms):
        """Hold a real returned-preparation syscall past its already-set budget.

        The host handshake must be observed before waiting out the budget. No
        clock is mocked, and a missed barrier/timeout is a failing test.
        """
        with tempfile.TemporaryDirectory(dir=self.root, prefix="barrier-") as directory:
            ready = Path(directory) / "ready"
            release = Path(directory) / "release"
            env = self.env(fault)
            env.update(TIMEOUT_PREP_READY=str(ready), TIMEOUT_PREP_RELEASE=str(release),
                       TIMEOUT_PREP_PATH=request.get("cancelPath", ""))
            process = subprocess.Popen([str(DRIVER)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                       stderr=subprocess.PIPE, text=True, env=env)
            try:
                process.stdin.write(json.dumps(request) + "\n")
                process.stdin.close()
                process.stdin = None
                self.wait_preparation(process, ready, budget_ms)
                release.touch()
                stdout, stderr = process.communicate(timeout=8)
                self.assertEqual(process.returncode, 0, stderr + stdout)
                return json.loads(stdout)
            finally:
                release.touch(exist_ok=True)
                if process.poll() is None:
                    process.kill()
                    process.communicate(timeout=3)

    def wait_preparation(self, process, ready, budget_ms):
        deadline = time.monotonic() + 3
        while not (ready.exists() and ready.read_text() == "ready"):
            self.assertIsNone(process.poll(), "worker exited before reaching preparation barrier")
            self.assertLess(time.monotonic(), deadline, "preparation barrier was not reached")
            time.sleep(0.005)
        # The adapter set its deadline before reaching this barrier. The delay
        # models returned blocking preparation, not an instantaneous OS cutoff.
        time.sleep((budget_ms + 100) / 1000)

    def test_local_deadline_preserves_partial_artifacts_without_target_exit_claim(self):
        result = self.tool()
        self.assertEqual(result["status"], "timedOut", result)
        partial = result["partialResult"]
        self.assertIsNone(partial["exitCode"])
        self.assertIsNone(partial["sha256"])
        self.assertEqual((self.workspace / "effect").read_text(), "x")
        self.assertEqual(len(partial["artifacts"]), 1)
        ref = partial["artifacts"][0]
        data = (self.session / "artifacts" / (ref["id"] + ".blob")).read_bytes()
        self.assertEqual(data, b"partial output\n")
        self.assertEqual(hashlib.sha256(data).hexdigest(), ref["sha256"])

    def test_detached_closed_stdio_child_is_stopped_at_return(self):
        result = self.tool(DETACHED, timeoutMs=1200)
        self.assertEqual(result["status"], "timedOut", result)
        self.assertIn("detached child ready", result["partialResult"]["text"])
        # The child holds this lock for its whole lifetime. No post-return sleep
        # is allowed to turn eventual cleanup into evidence of settled return.
        with (self.workspace / "lease").open("r+") as lease:
            fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)

    def test_host_and_invocation_deadlines_remain_interrupted(self):
        for options in [{"executionProfile": "host"}, {"localDeadline": False}]:
            with self.subTest(options=options):
                self.assertEqual(self.tool(**options)["status"], "interrupted")

    def test_cancellation_during_status_observation_overrides_local_timeout(self):
        self.assertEqual(self.tool(fault="cancel_at_status")["status"], "interrupted")
        self.assertTrue((self.session / "cancel").exists())

    def test_missing_malformed_reordered_duplicate_or_open_status_refuses_timeout(self):
        for fault in ["status_missing", "status_malformed", "status_reordered", "status_duplicate", "status_open"]:
            with self.subTest(fault=fault):
                self.assertEqual(self.tool(fault=fault)["status"], "uncertain")

    def test_scan_reap_cleanup_and_artifact_failures_refuse_timeout(self):
        for fault in ["scan_failure", "reap_failure", "cleanup_deadline", "artifact_failure"]:
            with self.subTest(fault=fault):
                result = self.tool(fault=fault)
                self.assertEqual(result["status"], "uncertain")
                if fault == "cleanup_deadline":
                    self.assertIn("cleanup deadline exceeded", result["text"])

    def test_wrong_procfs_view_refuses_before_launch(self):
        result = self.tool(fault="proc_mismatch")
        self.assertNotEqual(result["status"], "timedOut", result)
        self.assertFalse((self.workspace / "effect").exists())

    def test_returned_tool_preparation_cannot_reset_global_or_local_deadline(self):
        for limits in [{"timeoutMs": 3000, "invocationBudgetMs": 100}, {"timeoutMs": 100}]:
            with self.subTest(limits=limits):
                result = self.blocked_request(self.tool_request(**limits), "tool_preparation", 100)
                self.assertEqual(result["status"], "interrupted", result)
                self.assertFalse((self.workspace / "effect").exists(), "target launched after preparation expired")

    def test_returned_profile_preparation_cannot_reset_validation_allowance(self):
        request = {"op": "sandboxValidate", "workspace": str(self.workspace),
                   "session": str(self.session), "timeoutMs": 100}
        result = self.blocked_request(request, "tool_preparation", 100)
        self.assertEqual(result["status"], "failed", result)
        self.assertIn("deadline", result["error"])

    def test_returned_provider_preparation_cannot_dispatch_late_request(self):
        class Handler(http.server.BaseHTTPRequestHandler):
            def log_message(self, *_):
                pass

            def do_POST(handler):
                handler.server.requests += 1
                handler.rfile.read(int(handler.headers.get("Content-Length", "0")))
                handler.send_response(200)
                handler.send_header("Content-Length", "2")
                handler.end_headers()
                handler.wfile.write(b"{}")

        server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        server.daemon_threads = True
        server.requests = 0
        worker = threading.Thread(target=server.serve_forever, daemon=True)
        worker.start()
        try:
            for op in ["http", "modelStream"]:
                for limits in [{"timeoutMs": 3000, "invocationBudgetMs": 100}, {"timeoutMs": 100}]:
                    with self.subTest(op=op, limits=limits):
                        request = {"op": op, "payload": {}, "cancelPath": str(self.root / "absent-provider-cancel"),
                                   "endpoint": f"http://127.0.0.1:{server.server_port}/", **limits}
                        result = self.blocked_request(request, "provider_preparation", 100)
                        if op == "http":
                            self.assertEqual(result["status"], "interrupted", result)
                        else:
                            self.assertIn("interrupted", result["observation"], result)
                        self.assertEqual(server.requests, 0, "provider request dispatched after preparation expired")
        finally:
            server.shutdown()
            server.server_close()
            worker.join(timeout=2)

    def test_global_deadline_during_execution_is_not_local_timeout(self):
        result = self.tool(timeoutMs=3000, invocationBudgetMs=1000)
        self.assertEqual(result["status"], "interrupted", result)
        self.assertIn("invocation deadline", result["text"])
        self.assertEqual((self.workspace / "effect").read_text(), "x")

    def test_global_expiry_after_receipt_and_cancellation_priority(self):
        for fault in ["status_global", "cancel_global"]:
            with self.subTest(fault=fault):
                request = self.tool_request(timeoutMs=200, invocationBudgetMs=1000)
                result = self.blocked_request(request, fault, 1000)
                self.assertEqual(result["status"], "interrupted", result)
                self.assertIn("cancelled" if fault == "cancel_global" else "invocation deadline", result["text"])

    def cli_after_preparation_budget(self, binary=CLI):
        """Also usable unchanged with the archived pre-correction CLI."""
        self.prepare(operationTimeoutMs=3000, maxElapsedMs=500)
        ready, release = self.root / "cli-preparation-ready", self.root / "cli-preparation-release"
        env = self.env("cli_preparation")
        env.update(TIMEOUT_PREP_READY=str(ready), TIMEOUT_PREP_RELEASE=str(release))
        command = [str(binary), "run", "--workspace", str(self.workspace), "--session", str(self.session),
                   "--config", str(self.config), "--task", "Exercise returned preparation deadline",
                   "--script", str(self.script), "--json"]
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env=env)
        try:
            self.wait_preparation(process, ready, 500)
            release.touch()
            stdout, stderr = process.communicate(timeout=8)
            self.assertEqual(process.returncode, 4, stderr + stdout)
            return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
        finally:
            release.touch(exist_ok=True)
            if process.poll() is None:
                process.kill()
                process.communicate(timeout=3)

    def test_cli_does_not_launch_after_returned_preparation_exhausts_invocation(self):
        self.cli_after_preparation_budget()
        self.assertFalse((self.workspace / "effect").exists())
        self.assertFalse((self.workspace / "must-not-exist").exists())

    def cli(self, *args, fault=None, expected=0):
        result = subprocess.run([str(CLI), *map(str, args)], env=self.env(fault),
                                capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, expected, result.stderr + result.stdout)
        return result

    def prepare(self, **config):
        # Direct adapter fixtures own their session directory; CLI run creates
        # its fresh session atomically and must reject a pre-existing directory.
        self.session.rmdir()
        self.config = self.root / "config.json"
        self.config.write_text(json.dumps({"model": "scripted", "commands": "allow",
            "executionProfile": "bubblewrap", "operationTimeoutMs": 800, "maxElapsedMs": 20000,
            "maxModelAttempts": 6, "maxToolCalls": 8, **config}))
        self.script = self.root / "script.json"
        self.script.write_text(json.dumps([
            response([("deadline", "process", {"argv": ["/usr/bin/python3", "-c", SLEEP]}),
                      ("skipped", "create", {"path": "must-not-exist", "content": "unsafe queued mutation"})]),
            response([("inspect-effects", "read", {"path": "effect"})]), response(text="inspected partial effects")]))

    def run_cli(self, fault=None, expected=0):
        return self.cli("run", "--workspace", self.workspace, "--session", self.session,
                        "--config", self.config, "--task", "Exercise settled timeout", "--script", self.script,
                        "--json", fault=fault, expected=expected)

    def records(self):
        return [json.loads(line)["record"] for line in (self.session / "journal.jsonl").read_text().split("\n") if line]

    def inspect(self):
        value = json.loads(self.cli("inspect", self.session).stdout)
        self.assertEqual(value, json.loads(self.cli("replay", self.session).stdout))
        return value

    def assert_finished_batch(self):
        inspected = self.inspect()
        self.assertTrue(inspected["terminal"])
        self.assertFalse(inspected["pending"])
        self.assertEqual(inspected["state"]["toolDispatches"], 2)
        self.assertFalse((self.workspace / "must-not-exist").exists())
        self.assertEqual((self.workspace / "effect").read_text(), "x")
        tool_intents = [r["action"]["call"]["id"] for r in self.records()
                        if r["kind"] == "intent" and r["action"]["kind"] == "tool"]
        self.assertEqual(tool_intents, ["deadline", "inspect-effects"])
        results = [block for message in inspected["state"]["history"] for block in message["content"]
                   if block.get("type") == "tool_result"]
        self.assertEqual([r["tool_use_id"] for r in results], ["deadline", "skipped", "inspect-effects"])
        self.assertEqual([r["is_error"] for r in results], [True, True, False])

    def test_real_cli_aborts_batch_and_returns_to_model_inspection(self):
        self.prepare()
        self.run_cli()
        self.assert_finished_batch()

    def test_equal_operation_and_invocation_limit_remains_conservative(self):
        self.prepare(operationTimeoutMs=800, maxElapsedMs=800)
        self.run_cli(expected=4)
        self.assertFalse(any("timedOut" in r.get("observation", {}) for r in self.records()))
        self.assertFalse((self.workspace / "must-not-exist").exists())

    def test_crash_before_durable_timeout_keeps_unknown_intent_without_replay(self):
        self.prepare()
        self.run_cli(fault="before_completion", expected=86)
        self.assertTrue(self.inspect()["pending"])
        self.cli("resume", self.session, expected=2)
        self.assertEqual((self.workspace / "effect").read_text(), "x")
        self.assertFalse((self.workspace / "must-not-exist").exists())

    def test_durable_timeout_replays_and_cannot_be_resolved_or_repeated(self):
        self.prepare()
        self.run_cli(fault="after_completion", expected=86)
        inspected = self.inspect()
        self.assertFalse(inspected["pending"])
        self.assertIsNone(inspected["recoverableOperation"])
        completion = next(r for r in self.records() if "timedOut" in r.get("observation", {}))
        journal = self.session / "journal.jsonl"
        original = journal.read_bytes()
        self.cli("resolve", self.session, "--operation", completion["id"], "--status", "abandoned",
                 "--note", "must not reopen a settled timeout", "--resources-settled", expected=2)
        self.assertEqual(journal.read_bytes(), original)
        self.cli("resume", self.session)
        self.assert_finished_batch()


if __name__ == "__main__":
    unittest.main()
