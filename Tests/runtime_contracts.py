"""Linux adapter contracts against the compiled Lean test driver.

Python supplies temporary environments and independent assertions only. Production
execution does not call this file or use a JSON subprocess bridge.
"""
import hashlib
import http.server
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / ".lake/build/bin/runtime_contracts"

FAULT_SHIM = r"""
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>
static pid_t reaped_child = 0;
pid_t waitpid(pid_t pid, int *status, int options) {
    static pid_t (*real_waitpid)(pid_t,int*,int);
    if (!real_waitpid) real_waitpid = dlsym(RTLD_NEXT, "waitpid");
    pid_t result = real_waitpid(pid, status, options);
    if (result > 0) {
        reaped_child = result;
        if (getenv("HARNESS_TEST_WAIT_ERROR_AFTER_REAP")) { errno = ECHILD; return -1; }
    }
    return result;
}
int kill(pid_t pid, int signal) {
    static int (*real_kill)(pid_t,int);
    if (!real_kill) real_kill = dlsym(RTLD_NEXT, "kill");
    const char *marker = getenv("HARNESS_TEST_SIGNAL_AFTER_REAP");
    if (marker && reaped_child && pid == -reaped_child) {
        int fd = open(marker, O_WRONLY | O_CREAT | O_APPEND, 0600);
        if (fd >= 0) { ssize_t written = write(fd, "signal-after-reap\n", 18); (void)written; close(fd); }
    }
    return real_kill(pid, signal);
}
int fsync(int fd) {
    static int (*real_fsync)(int);
    if (!real_fsync) real_fsync = dlsym(RTLD_NEXT, "fsync");
    struct stat s;
    if (getenv("HARNESS_TEST_FAIL_FSYNC") ||
        (getenv("HARNESS_TEST_FAIL_DIRECTORY_FSYNC") && fstat(fd, &s) == 0 && S_ISDIR(s.st_mode))) {
        errno = ENOSPC; return -1;
    }
    return real_fsync(fd);
}
ssize_t write(int fd, const void *data, size_t size) {
    static ssize_t (*real_write)(int,const void*,size_t);
    if (!real_write) real_write = dlsym(RTLD_NEXT, "write");
    if (getenv("HARNESS_TEST_FAIL_ARTIFACT_WRITE")) {
        char path[64], target[4096];
        snprintf(path, sizeof(path), "/proc/self/fd/%d", fd);
        ssize_t n = readlink(path, target, sizeof(target)-1);
        if (n >= 0) {
            target[n] = 0;
            if (strstr(target, "/artifacts/")) { errno = ENOSPC; return -1; }
        }
    }
    return real_write(fd, data, size);
}
"""


class Contracts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.shim_temp = tempfile.TemporaryDirectory()
        directory = Path(cls.shim_temp.name)
        source = directory / "faults.c"
        source.write_text(FAULT_SHIM)
        cls.shim = directory / "faults.so"
        subprocess.run(["cc", "-shared", "-fPIC", "-O2", str(source), "-o", str(cls.shim), "-ldl"], check=True)

    @classmethod
    def tearDownClass(cls):
        cls.shim_temp.cleanup()

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.workspace = self.root / "workspace"
        self.workspace.mkdir()
        self.artifacts = self.root / "artifacts"

    def tearDown(self):
        self.temp.cleanup()

    def call(self, request, env=None, timeout=10, pass_fds=(), preexec_fn=None):
        result = subprocess.run([str(BIN)], input=json.dumps(request) + "\n", text=True,
                                capture_output=True, cwd=ROOT, env=env, timeout=timeout,
                                start_new_session=True, pass_fds=pass_fds, preexec_fn=preexec_fn)
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertEqual(len(result.stdout.splitlines()), 1, result.stdout)
        return json.loads(result.stdout)

    def request(self, name, args, **options):
        return {"op": "tool", "workspace": str(self.workspace), "call": {"name": name, "args": args},
                "artifactDir": str(self.artifacts), **options}

    def run_tool(self, name, args, env=None, **options):
        return self.call(self.request(name, args, **options), env=env)

    def fault_env(self, name):
        return {**os.environ, "LD_PRELOAD": str(self.shim), name: "1"}

    def test_read_edit_preimage_and_exact_match(self):
        path = self.workspace / "main.py"
        path.write_text("def add(a, b):\n    return a - b\n")
        read = self.run_tool("read", {"path": "main.py"})
        self.assertEqual(read["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
        args = {"path": "main.py", "old": "return a - b", "new": "return a + b", "expectedSha256": read["sha256"]}
        self.assertEqual(self.run_tool("edit", args)["status"], "ok")
        self.assertIn("return a + b", path.read_text())
        stale = self.run_tool("edit", args)
        self.assertEqual(stale["status"], "failed")
        self.assertIn("preimage changed", stale["text"])
        path.write_text("same same")
        ambiguous = self.run_tool("edit", {"path": "main.py", "old": "same", "new": "x",
                                          "expectedSha256": hashlib.sha256(path.read_bytes()).hexdigest()})
        self.assertEqual(ambiguous["status"], "failed")
        self.assertIn("exactly once", ambiguous["text"])
        self.assertEqual(path.read_text(), "same same")

    def test_path_symlink_and_overwrite_rejection(self):
        outside = self.root / "outside"
        outside.write_text("secret")
        (self.workspace / "link").symlink_to(outside)
        (self.workspace / "dirlink").symlink_to(self.root, target_is_directory=True)
        for path in ["../outside", str(outside), "link", "dirlink/outside"]:
            with self.subTest(path=path):
                self.assertEqual(self.run_tool("read", {"path": path})["status"], "failed")
        self.assertEqual(self.run_tool("create", {"path": "new.txt", "content": "first"})["status"], "ok")
        self.assertEqual(self.run_tool("create", {"path": "new.txt", "content": "second"})["status"], "failed")
        self.assertEqual((self.workspace / "new.txt").read_text(), "first")
        self.assertEqual(outside.read_text(), "secret")
        result = self.run_tool("process", {"argv": [sys.executable, "-c", "open('escaped','w').write('x')"], "cwd": "dirlink"})
        self.assertEqual(result["status"], "failed")
        self.assertFalse((self.root / "escaped").exists())

    def test_list_search_are_stable_bounded_and_ignore_paths(self):
        (self.workspace / "z.txt").write_text("Needle needle")
        (self.workspace / "a.txt").write_text("needle")
        (self.workspace / ".git").mkdir()
        (self.workspace / ".git" / "secret").write_text("needle")
        self.assertEqual(self.run_tool("list", {})["text"], "a.txt\nz.txt")
        matches = self.run_tool("search", {"query": "needle", "limit": 1})["text"]
        self.assertTrue(matches.startswith("a.txt:1:needle"), matches)
        self.assertIn("limit reached", matches)

    def test_search_single_file(self):
        (self.workspace / "one.txt").write_text("find me\n")
        self.assertIn("one.txt:1:find me", self.run_tool("search", {"path": "one.txt", "query": "find"})["text"])

    def test_process_separate_launcher_and_exit_failure(self):
        result = self.run_tool("process", {"argv": [sys.executable, "-c", "import sys;print('failed test');sys.exit(7)"]})
        self.assertEqual(result["status"], "ok", result)
        self.assertEqual(result["exitCode"], 7)
        self.assertIn("failed test", result["text"])
        self.assertEqual(self.run_tool("process", {"argv": ["/definitely/not/a/program"]})["status"], "failed")
        genuine255 = self.run_tool("process", {"argv": [sys.executable, "-c", "import sys;sys.exit(255)"]})
        self.assertEqual(genuine255["status"], "ok", genuine255)
        self.assertEqual(genuine255["exitCode"], 255)
        no_exec = self.workspace / "not-executable"
        no_exec.write_text("not a program")
        self.assertEqual(self.run_tool("process", {"argv": [str(no_exec)]})["status"], "failed")
        bad_interpreter = self.workspace / "bad-interpreter"
        bad_interpreter.write_text("#!/definitely/not/an/interpreter\n")
        bad_interpreter.chmod(0o700)
        self.assertEqual(self.run_tool("process", {"argv": [str(bad_interpreter)]})["status"], "failed")

    def test_process_stdin_is_closed(self):
        result = self.run_tool("process", {"argv": [sys.executable, "-c", "import sys; print('eof',repr(sys.stdin.read()))"]}, timeoutMs=1000)
        self.assertEqual(result["status"], "ok", result)
        self.assertIn("eof ''", result["text"])

    def test_process_does_not_inherit_unrelated_descriptors(self):
        import fcntl
        secret = self.root / "private-descriptor"
        secret.write_text("descriptor-only-secret")
        original = os.open(secret, os.O_RDONLY)
        try:
            inherited = fcntl.fcntl(original, fcntl.F_DUPFD, 200)
        finally:
            os.close(original)
        try:
            code = (f"import os\ntry:\n data=os.read({inherited},100)\n"
                    "except OSError:\n print('closed')\nelse:\n print(repr(data))")
            request = self.request("process", {"argv": [sys.executable, "-c", code]})
            result = self.call(request, pass_fds=(inherited,))
            self.assertEqual(result["status"], "ok", result)
            self.assertEqual(result["exitCode"], 0)
            self.assertIn("closed", result["text"])
            self.assertNotIn("descriptor-only-secret", result["text"])
        finally:
            os.close(inherited)

    def test_large_output_bounded_artifact_and_unicode(self):
        code = "import sys; sys.stdout.write('🦉' * 100000);sys.stderr.write('error-output' * 20000)"
        result = self.run_tool("process", {"argv": [sys.executable, "-c", code]}, outputBytes=1024)
        self.assertEqual(result["status"], "ok", result)
        self.assertEqual(result["exitCode"], 0)
        self.assertLess(len(result["text"].encode()), 1500)
        self.assertIn("truncated", result["text"])
        artifacts = {item["label"]: item for item in result["artifacts"]}
        self.assertGreater(sum(item["storedBytes"] for item in artifacts.values()), 600000)
        stdout = (self.artifacts / (artifacts["stdout"]["id"] + ".blob")).read_bytes()
        stderr = (self.artifacts / (artifacts["stderr"]["id"] + ".blob")).read_bytes()
        self.assertEqual(stdout, "🦉".encode() * 100000)
        self.assertEqual(stderr, b"error-output" * 20000)
        result["text"].encode("utf-8")

    def test_full_duplex_capture_drains_while_sending_input(self):
        marker = self.root / "input-size"
        code = ("import sys;sys.stdout.write('O'*200000);sys.stdout.flush();"
                "sys.stderr.write('E'*200000);sys.stderr.flush();"
                f"data=sys.stdin.buffer.read();open({str(marker)!r},'w').write(str(len(data)))")
        result = self.call({"op": "capture", "cmd": sys.executable, "args": ["-c", code],
                            "input": "x" * 200000, "stdoutBytes": 1024, "stderrBytes": 2048,
                            "timeoutMs": 3000})
        self.assertEqual(result["status"], "ok", result)
        self.assertEqual(result["exitCode"], 0)
        self.assertEqual(result["stdout"], "O" * 1024)
        self.assertEqual(result["stderr"], "E" * 2048)
        self.assertEqual(result["stdoutTotal"], 200000)
        self.assertEqual(result["stderrTotal"], 200000)
        self.assertEqual(marker.read_text(), "200000")

    def test_artifact_retention_is_bounded(self):
        code = "import sys;sys.stdout.buffer.write(b'x'*(17*1024*1024))"
        result = self.run_tool("process", {"argv": [sys.executable, "-c", code]}, outputBytes=512, timeoutMs=6000)
        self.assertEqual(result["status"], "ok", result)
        artifact = next(item for item in result["artifacts"] if item["label"] == "stdout")
        self.assertEqual(artifact["storedBytes"], 16 * 1024 * 1024)
        self.assertEqual((self.artifacts / (artifact["id"] + ".blob")).stat().st_size, artifact["storedBytes"])
        self.assertTrue(artifact["truncated"])
        self.assertEqual(artifact["totalBytes"], 17 * 1024 * 1024)

    def test_deadline_kills_ignoring_process(self):
        before = time.monotonic()
        code = "import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);print('started',flush=True);time.sleep(20)"
        result = self.run_tool("process", {"argv": [sys.executable, "-c", code]}, timeoutMs=150)
        self.assertEqual(result["status"], "interrupted", result)
        self.assertLess(time.monotonic() - before, 3)
        self.assertIn("may have changed files", result["text"])

    def test_residual_process_group_is_uncertain_and_killed(self):
        code = "import subprocess,sys; p=subprocess.Popen([sys.executable,'-c','import time;time.sleep(20)'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL);open('descendant','w').write(str(p.pid))"
        result = self.run_tool("process", {"argv": [sys.executable, "-c", code]}, timeoutMs=1000)
        self.assertEqual(result["status"], "uncertain", result)
        pid = int((self.workspace / "descendant").read_text())
        stat = Path(f"/proc/{pid}/stat")
        if stat.exists():
            self.assertEqual(stat.read_text().split(") ", 1)[1][0], "Z", "descendant is still executing")

    def test_no_group_signal_after_leader_identity_is_reaped(self):
        for inject_wait_error in [False, True]:
            with self.subTest(inject_wait_error=inject_wait_error):
                marker = self.root / "signal-after-reap"
                env = {**os.environ, "LD_PRELOAD": str(self.shim),
                       "HARNESS_TEST_SIGNAL_AFTER_REAP": str(marker)}
                if inject_wait_error:
                    env["HARNESS_TEST_WAIT_ERROR_AFTER_REAP"] = "1"
                result = self.run_tool("process", {"argv": [sys.executable, "-c", "print('done')"]}, env=env)
                self.assertEqual(result["status"], "uncertain" if inject_wait_error else "ok", result)
                self.assertFalse(marker.exists(), "supervisor signaled a potentially reused process group identity")

    def test_inherited_sigchld_ignore_does_not_autoreap_child(self):
        import signal
        request = self.request("process", {"argv": [sys.executable, "-c", "print('waitable child')"]})
        result = self.call(request, preexec_fn=lambda: signal.signal(signal.SIGCHLD, signal.SIG_IGN))
        self.assertEqual(result["status"], "ok", result)
        self.assertEqual(result["exitCode"], 0)
        self.assertIn("waitable child", result["text"])

    def test_cancel_before_dispatch_does_not_write(self):
        cancel = self.root / "cancel"
        cancel.touch()
        for name, args in [("create", {"path": "absent", "content": "x"}),
                           ("process", {"argv": [sys.executable, "-c", "open('absent','w').write('x')"]})]:
            result = self.run_tool(name, args, cancelPath=str(cancel))
            self.assertEqual(result["status"], "interrupted", result)
            self.assertFalse((self.workspace / "absent").exists())

    def test_session_creation_is_exclusive(self):
        session = self.root / "parent" / "session"
        self.assertEqual(self.call({"op": "sessionCreate", "path": str(session)})["status"], "ok")
        self.assertEqual(session.stat().st_mode & 0o777, 0o700)
        self.assertEqual(self.call({"op": "sessionCreate", "path": str(session)})["status"], "failed")

    def test_approval_without_terminal_denies(self):
        result = self.call({"op": "approval"})
        self.assertFalse(result["approved"])

    def test_approval_real_controlling_terminal(self):
        import fcntl
        import pty
        import termios
        cases = [(b"yes\n", "approved"), (b" yes\n", "denied"), (b"YES\n", "denied"),
                 (b"yes \n", "denied"), (b"no\n", "denied"), (b"y" * 128 + b"\n", "denied"), (None, "interrupted")]
        for answer, expected in cases:
            with self.subTest(answer=answer):
                master, slave = pty.openpty()
                def controlling_terminal():
                    os.setsid()
                    fcntl.ioctl(slave, termios.TIOCSCTTY, 0)
                child = subprocess.Popen([str(BIN)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                         stderr=subprocess.PIPE, pass_fds=(slave,), preexec_fn=controlling_terminal)
                os.close(slave)
                try:
                    if answer is not None:
                        os.write(master, answer)
                    out, err = child.communicate(json.dumps({"op": "approval", "timeoutMs": 150}).encode() + b"\n", timeout=3)
                    self.assertEqual(child.returncode, 0, err)
                    result = json.loads(out)
                    if expected == "interrupted":
                        self.assertEqual(result["status"], "interrupted")
                    else:
                        self.assertEqual(result["approved"], expected == "approved", result)
                finally:
                    os.close(master)
                    if child.poll() is None:
                        child.kill()
                        child.wait()

    def test_approval_cancellation(self):
        cancel = self.root / "cancel"
        cancel.touch()
        result = self.call({"op": "approval", "cancelPath": str(cancel)})
        self.assertEqual(result["status"], "interrupted")
        self.assertFalse(result["approved"])

    def test_journal_hash_chain_incomplete_tail_and_corruption(self):
        journal = self.root / "session" / "journal"
        for kind in ["intent", "completion"]:
            self.assertEqual(self.call({"op": "journalAppend", "path": str(journal), "record": {"kind": kind, "id": 1}})["status"], "ok")
        result = self.call({"op": "journalRead", "path": str(journal)})
        self.assertEqual(len(result["records"]), 2)
        with journal.open("ab") as file:
            file.write(b'{"partial"')
        self.assertTrue(self.call({"op": "journalRead", "path": str(journal)})["interrupted"])
        self.assertEqual(self.call({"op": "journalAppend", "path": str(journal), "record": {"kind": "terminal"}})["status"], "failed")
        contents = journal.read_bytes()
        self.assertIn(b'"id":1', contents)
        journal.write_bytes(contents.replace(b'"id":1', b'"id":9', 1))
        self.assertEqual(self.call({"op": "journalRead", "path": str(journal)})["status"], "failed")

    def test_file_flush_failure_after_replacement_is_uncertain(self):
        path = self.workspace / "new"
        path.write_text("before")
        result = self.run_tool("create", {"path": "new", "content": "after", "overwrite": True},
                               env=self.fault_env("HARNESS_TEST_FAIL_DIRECTORY_FSYNC"))
        self.assertEqual(result["status"], "uncertain", result)
        self.assertEqual(path.read_text(), "after", "fixture must fail after replacement")

    def test_journal_flush_failure_is_visible(self):
        path = self.root / "journal"
        result = self.call({"op": "journalAppend", "path": str(path), "record": {"kind": "intent", "id": 1}},
                           env=self.fault_env("HARNESS_TEST_FAIL_FSYNC"))
        self.assertEqual(result["status"], "failed", result)

    def test_output_storage_failure_after_launch_is_uncertain(self):
        result = self.run_tool("process", {"argv": [sys.executable, "-c", "print('output',flush=True)"]},
                               outputBytes=1, env=self.fault_env("HARNESS_TEST_FAIL_ARTIFACT_WRITE"))
        self.assertEqual(result["status"], "uncertain", result)
        self.assertIn("after process launch", result["text"])

    def test_process_does_not_inherit_provider_credential(self):
        env = {**os.environ, "ANTHROPIC_API_KEY": "test-only-secret", "SSLKEYLOGFILE": "test-only-secret"}
        result = self.run_tool("process", {"argv": [sys.executable, "-c", "import os;print('ANTHROPIC_API_KEY' in os.environ);print('SSLKEYLOGFILE' in os.environ)"]}, env=env)
        self.assertEqual(result["status"], "ok", result)
        self.assertIn("False", result["text"])
        self.assertNotIn("test-only-secret", result["text"])
        self.assertNotIn("True", result["text"])

    def test_test_driver_emits_one_observation(self):
        self.assertEqual(self.run_tool("list", {})["status"], "ok")

    def test_http_real_loopback_status_cap_redirect_and_no_credentials(self):
        requests = []
        class Server(http.server.BaseHTTPRequestHandler):
            def do_POST(self):
                body = self.rfile.read(int(self.headers.get("Content-Length", 0)))
                requests.append((self.path, self.headers.get("x-api-key"), body))
                if self.path == "/redirect":
                    self.send_response(302)
                    self.send_header("Location", "https://example.invalid/")
                    self.end_headers()
                    return
                self.send_response(429 if self.path == "/rate" else 200)
                self.end_headers()
                self.wfile.write(b'{"message":"hello"}')
            def log_message(self, *args):
                pass
        server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Server)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            base = f"http://127.0.0.1:{server.server_port}"
            request = {"op": "http", "payload": {"input": "x" * 100000}, "endpoint": base + "/rate"}
            env = {**os.environ, "ANTHROPIC_API_KEY": "must-not-reach-loopback"}
            self.assertEqual(self.call(request, env=env)["httpStatus"], 429)
            request["responseBytes"] = 3
            self.assertEqual(self.call(request)["status"], "uncertain")
            request.pop("responseBytes")
            request["endpoint"] = base + "/redirect"
            self.assertEqual(self.call(request)["httpStatus"], 302)
            request["endpoint"] = "https://attacker.invalid/messages"
            self.assertEqual(self.call(request)["status"], "failed")
            self.assertEqual(len(requests), 3, "transport must not retry or follow redirects")
            self.assertTrue(all(key is None for _, key, _ in requests), requests)
            self.assertTrue(all(json.loads(body)["input"] == "x" * 100000 for _, _, body in requests))
        finally:
            server.shutdown()
            server.server_close()
            thread.join()


if __name__ == "__main__":
    unittest.main()
