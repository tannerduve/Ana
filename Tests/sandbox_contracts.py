"""Actual bubblewrap boundary probes against the Lean/Rust adapter; no model calls."""
import hashlib
import json
import os
from pathlib import Path
import signal
import socket
import subprocess
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / ".lake/build/bin/runtime_contracts"


_LOCALHOST_PROBE = r"""import http.client
import http.server
import json
import os
from pathlib import Path
import socket
import threading

# Bound default local DNS fallback delay; no remote names are requested.
os.environ["RES_OPTIONS"] = "attempts:1 timeout:1"
result = {
    "files": {p: Path(p).exists() for p in ["/etc/hosts", "/etc/nsswitch.conf", "/etc/resolv.conf"]},
    "getaddrinfo": {},
    "http": {},
}
for host in ["localhost", "127.0.0.1", "::1"]:
    try:
        rows = socket.getaddrinfo(host, 0, type=socket.SOCK_STREAM)
        result["getaddrinfo"][host] = {"ok": True, "addresses": sorted({str(row[4][0]) for row in rows})}
    except OSError as error:
        result["getaddrinfo"][host] = {
            "ok": False, "type": type(error).__name__, "errno": error.errno, "message": str(error),
        }


class Handler(http.server.BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def do_GET(self):
        body = b"local-only marker"
        self.send_response(200)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


server = http.server.HTTPServer(("127.0.0.1", 0), Handler)
thread = threading.Thread(target=server.serve_forever, daemon=True)
thread.start()
try:
    for host in ["127.0.0.1", "localhost"]:
        connection = http.client.HTTPConnection(host, server.server_port, timeout=2)
        try:
            connection.request("GET", "/")
            response = connection.getresponse()
            result["http"][host] = {"ok": True, "status": response.status, "body": response.read().decode()}
        except OSError as error:
            result["http"][host] = {
                "ok": False, "type": type(error).__name__, "errno": error.errno, "message": str(error),
            }
        finally:
            connection.close()
finally:
    server.shutdown()
    server.server_close()
    thread.join()
try:
    alternate = http.server.HTTPServer(("localhost", 0), Handler)
except OSError as error:
    result["bind_localhost"] = {
        "ok": False, "type": type(error).__name__, "errno": error.errno, "message": str(error),
    }
else:
    result["bind_localhost"] = {"ok": True, "address": alternate.server_address[0]}
    alternate.server_close()
print(json.dumps(result, sort_keys=True))
"""


class SandboxContracts(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.workspace = self.root / "workspace"
        self.workspace.mkdir()
        self.session = self.root / "session"
        self.session.mkdir()

    def tearDown(self):
        self.temporary.cleanup()

    def call(self, request, **kwargs):
        result = subprocess.run([str(BIN)], input=json.dumps(request) + "\n",
                                text=True, capture_output=True, timeout=12, **kwargs)
        self.assertEqual(result.returncode, 0, result.stderr)
        return json.loads(result.stdout)

    def validate(self, roots=()):
        return self.call({"op": "sandboxValidate", "workspace": str(self.workspace),
                          "session": str(self.session), "toolchainRoots": list(roots)})

    def request(self, argv, **options):
        return {"op": "tool", "workspace": str(self.workspace), "executionProfile": "bubblewrap",
                "artifactDir": str(self.session / "artifacts"), "cancelPath": str(self.session / "cancel"),
                "timeoutMs": 3000, "call": {"name": "process", "args": {"argv": argv}}, **options}

    def run_code(self, code, **options):
        return self.call(self.request(["/usr/bin/python3", "-c", code], **options))

    def test_profile_and_ordinary_exit_statuses(self):
        self.assertEqual(self.validate()["status"], "ok")
        for code in [0, 1, 255]:
            with self.subTest(code=code):
                result = self.call(self.request(["/usr/bin/sh", "-c", f"exit {code}"]))
                self.assertEqual(result["status"], "ok", result)
                self.assertEqual(result["exitCode"], code)
        missing = self.call(self.request(["/missing-executable"]))
        self.assertEqual(missing["status"], "uncertain", missing)
        self.assertIn("completion was not established", missing["text"])

    def test_same_workspace_and_safe_relative_symlink(self):
        (self.workspace / "original").write_text("before")
        (self.workspace / "alias").symlink_to("original")
        (self.workspace / "absolute-alias").symlink_to(self.workspace / "original")
        self.assertEqual(self.validate()["status"], "ok")
        result = self.run_code(f"import pathlib; assert pathlib.Path.cwd()==pathlib.Path({str(self.workspace)!r}); "
                               "pathlib.Path('/workspace/alias').write_text('after'); "
                               "assert pathlib.Path('absolute-alias').read_text()=='after'; "
                               "assert pathlib.Path('/workspace/original').stat().st_ino==pathlib.Path('original').stat().st_ino")
        self.assertEqual(result["status"], "ok", result)
        self.assertEqual(result["exitCode"], 0, result)
        self.assertEqual((self.workspace / "original").read_text(), "after")
        read = self.call({**self.request([]), "call": {"name": "read", "args": {"path": "original"}}})
        self.assertIn("after", read["text"])

    def test_reserved_destination_guards_and_exact_workspace_alias(self):
        """Outer fixed fixture mappings test canonical names without host mkdirs."""
        sentinel = self.workspace / "unchanged"
        sentinel.write_text("before")
        for destination, expected in [("/workspace", "ok"), ("/workspace/nested", "failed"),
                                      ("/tmp/home/project", "failed"), ("/tmp", "failed"),
                                      ("/opt/harness", "failed"), ("/etc", "failed"),
                                      ("/etc/project", "failed")]:
            with self.subTest(destination=destination):
                request = {"op": "sandboxValidate", "workspace": destination,
                           "session": "/session", "toolchainRoots": []}
                command = ["/usr/bin/bwrap", "--unshare-user", "--unshare-pid", "--unshare-net",
                           "--die-with-parent", "--ro-bind", "/usr", "/usr", "--ro-bind", "/lib", "/lib",
                           "--ro-bind", "/lib64", "/lib64", "--symlink", "usr/bin", "/bin",
                           "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp",
                           "--ro-bind", str(BIN), "/driver",
                           "--bind", str(self.session), "/session", "--bind", str(self.workspace), destination,
                           "--setenv", "HOME", "/private-home", "--", "/driver"]
                result = subprocess.run(command, input=json.dumps(request)+"\n", text=True,
                                        capture_output=True, timeout=12)
                self.assertEqual(result.returncode, 0, result.stderr)
                observation = json.loads(result.stdout)
                self.assertEqual(observation["status"], expected, observation)
                if expected == "failed":
                    self.assertIn("reserved sandbox paths", observation["error"])
                self.assertEqual(sorted(p.name for p in self.workspace.iterdir()), ["unchanged"])
                self.assertEqual(sentinel.read_text(), "before")

    def test_preflight_rejects_host_aliases_and_special_files(self):
        outside = self.root / "outside"
        outside.write_text("unchanged")
        cases = [("hardlink", lambda p: os.link(outside, p)),
                 ("escape", lambda p: p.symlink_to("../outside")),
                 ("fifo", lambda p: os.mkfifo(p)),
                 ("git", lambda p: p.write_text("gitdir: ../external.git\n"))]
        for name, create in cases:
            path = self.workspace / (".git" if name == "git" else name)
            with self.subTest(name=name):
                create(path)
                try: self.assertEqual(self.validate()["status"], "failed")
                finally: path.unlink()
        with socket.socket(socket.AF_UNIX) as server:
            path = self.workspace / "service.sock"
            server.bind(str(path))
            self.assertEqual(self.validate()["status"], "failed")
        path.unlink()
        self.assertEqual(outside.read_text(), "unchanged")

    def test_host_secrets_session_fds_and_network_are_absent(self):
        secret = self.root / "host-secret"
        secret.write_text("fixture-secret-do-not-forward")
        (self.session / "journal.jsonl").write_text("private session fixture")
        with socket.socket() as listener, secret.open() as inherited:
            listener.bind(("127.0.0.1", 0)); listener.listen()
            code = f"""import os,pathlib,socket
assert not pathlib.Path({str(secret)!r}).exists()
assert not pathlib.Path({str(self.session)!r}).exists()
assert os.environ.get('ANTHROPIC_API_KEY') is None
assert os.environ['HOME']=='/tmp/home'
assert os.environ['TMPDIR']=='/tmp'
for fd in range(3,64):
 try:
  os.fstat(fd)
 except OSError: continue
 raise AssertionError('setup or inherited descriptor leaked')
try:
 connection=socket.create_connection(('127.0.0.1',{listener.getsockname()[1]}),timeout=.2)
except OSError: pass
else: raise AssertionError('host network reachable')
assert pathlib.Path('/proc/1/cmdline').read_bytes().find(b'bwrap')>=0
print('isolated')
"""
            result = self.call(self.request(["/usr/bin/python3", "-c", code]),
                               pass_fds=(inherited.fileno(),), env={**os.environ, "ANTHROPIC_API_KEY": "fixture-key"})
            self.assertEqual(result["status"], "ok", result)
            self.assertEqual(result["exitCode"], 0, result)
            self.assertIn("isolated", result["text"])

    def test_explicit_readonly_toolchain_and_launcher_not_from_path(self):
        toolchain = self.root / "toolchain"
        (toolchain / "bin").mkdir(parents=True)
        marker = toolchain / "bin" / "fixture-tool"
        marker.write_text("#!/bin/sh\nprintf toolchain-ok\\n\n"); marker.chmod(0o755)
        fake = self.workspace / "bwrap"
        fake.write_text("#!/bin/sh\ntouch escaped-launcher\nexit 0\n"); fake.chmod(0o755)
        self.assertEqual(self.validate([str(toolchain)])["status"], "ok")
        result = self.call(self.request(["/usr/bin/sh", "-c",
            "fixture-tool; printf changed > /opt/harness/toolchains/0/bin/fixture-tool"],
            toolchainRoots=[str(toolchain)]), env={**os.environ, "PATH": str(self.workspace)})
        self.assertEqual(result["status"], "ok", result)
        self.assertNotEqual(result["exitCode"], 0)
        self.assertIn("toolchain-ok", result["text"])
        self.assertFalse((self.workspace / "escaped-launcher").exists())
        self.assertTrue(marker.read_text().startswith("#!/bin/sh"))
        self.assertEqual(self.validate([str(self.session)])["status"], "failed")

    def test_raw_artifacts_preserve_split_utf8_and_shared_quota(self):
        code = "import os,time; os.write(1,b'A'*100+b'\\xe2'); time.sleep(.04); os.write(1,b'\\x82\\xac'); os.write(2,b'B'*100)"
        result = self.run_code(code, outputBytes=16, maxArtifactBytes=128, maxSessionArtifactBytes=256)
        self.assertEqual(result["status"], "ok", result)
        refs = {ref["label"]: ref for ref in result["artifacts"]}
        for label, expected in [("stdout", b"A"*100+"€".encode()), ("stderr", b"B"*100)]:
            ref = refs[label]
            actual = (self.session / "artifacts" / (ref["id"]+".blob")).read_bytes()
            self.assertEqual(actual, expected)
            self.assertEqual(ref["sha256"], hashlib.sha256(expected).hexdigest())
        limited = self.run_code("import os; os.write(1,b'x'*200); os.write(2,b'y'*200)",
                                outputBytes=16, maxArtifactBytes=128, maxSessionArtifactBytes=256)
        self.assertEqual(limited["status"], "ok", limited)
        self.assertEqual(sum(x["storedBytes"] for x in limited["artifacts"]), 53)

    def _detached(self, kill_runner):
        marker = self.workspace / "heartbeat"
        code = """import os,signal,time
if os.fork()==0:
 os.setsid(); signal.signal(signal.SIGTERM,signal.SIG_IGN)
 fd=os.open('/dev/null',os.O_RDWR)
 for n in (0,1,2): os.dup2(fd,n)
 while True:
  with open('/workspace/heartbeat','a') as out: out.write('x')
  time.sleep(.02)
time.sleep(60)
"""
        process = subprocess.Popen([str(BIN)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, text=True)
        try:
            process.stdin.write(json.dumps(self.request(["/usr/bin/python3", "-c", code], timeoutMs=5000))+"\n")
            process.stdin.close(); process.stdin = None
            deadline = time.monotonic()+4
            while not marker.exists() and time.monotonic()<deadline: time.sleep(.01)
            self.assertTrue(marker.exists())
            if kill_runner: process.kill()
            else: (self.session / "cancel").write_text("cancel")
            stdout, stderr = process.communicate(timeout=5)
            if not kill_runner:
                self.assertEqual(process.returncode, 0, stderr)
                self.assertIn(json.loads(stdout)["status"], {"interrupted", "uncertain"})
            time.sleep(.15)
            settled = marker.stat().st_size
            time.sleep(.15)
            self.assertEqual(marker.stat().st_size, settled, "detached child survived cleanup")
        finally:
            if process.poll() is None: process.kill(); process.wait(timeout=3)

    def test_detached_child_stops_on_cancellation(self):
        self._detached(False)

    def test_detached_child_stops_after_runner_death(self):
        self._detached(True)

    def test_localhost_resolves_binds_and_serves_same_sandbox_http(self):
        (self.workspace / "probe.py").write_text(_LOCALHOST_PROBE)
        result = self.call(self.request(["/usr/bin/python3", "probe.py"], timeoutMs=6000))
        self.assertEqual((result["status"], result["exitCode"]), ("ok", 0), result)
        value = json.loads(result["text"].removeprefix("[stdout] "))
        addresses = set(value["getaddrinfo"]["localhost"]["addresses"])
        self.assertIn("127.0.0.1", addresses)
        self.assertLessEqual(addresses, {"127.0.0.1", "::1"})
        self.assertTrue(value["getaddrinfo"]["127.0.0.1"]["ok"])
        self.assertTrue(value["getaddrinfo"]["::1"]["ok"])
        self.assertTrue(value["bind_localhost"]["ok"])
        for host in ["localhost", "127.0.0.1"]:
            self.assertEqual(value["http"][host], {"ok": True, "status": 200, "body": "local-only marker"})

    def test_fixed_data_readonly_no_host_configuration_external_dns_or_setup_fds(self):
        code = r"""import errno
import json
import os
import pathlib
import socket

expected = {
    "/etc/hosts": "127.0.0.1 localhost\n::1 localhost\n",
    "/etc/nsswitch.conf": "hosts: files\n",
}
for name, text in expected.items():
    assert pathlib.Path(name).read_text() == text
    for operation in ["write", "unlink", "rename"]:
        try:
            if operation == "write":
                pathlib.Path(name).write_text("tampered")
            elif operation == "unlink":
                pathlib.Path(name).unlink()
            else:
                pathlib.Path(name).rename(name + ".moved")
        except OSError as error:
            assert error.errno in [errno.EROFS, errno.EBUSY, errno.EACCES, errno.EPERM], error
        else:
            raise AssertionError("fixed configuration mutable: " + operation)
    assert pathlib.Path(name).read_text() == text
assert sorted(p.name for p in pathlib.Path("/etc").iterdir()) == ["hosts", "nsswitch.conf"]
for fd in range(3, 128):
    try:
        os.fstat(fd)
    except OSError:
        continue
    raise AssertionError("setup descriptor leaked")
try:
    socket.getaddrinfo("external-fixture.invalid", 80, type=socket.SOCK_STREAM)
except socket.gaierror as error:
    dns_error = error.errno
else:
    raise AssertionError("external name unexpectedly resolved")
try:
    socket.create_connection(("198.51.100.1", 9), timeout=.2)
except OSError as error:
    network_error = error.errno
else:
    raise AssertionError("external network unexpectedly reachable")
assert network_error == errno.ENETUNREACH, network_error
print(json.dumps({"fixed_readonly": True, "external_dns_errno": dns_error,
                  "external_network_errno": network_error, "setup_fds_absent": True}))
"""
        result = self.run_code(code)
        self.assertEqual((result["status"], result["exitCode"]), ("ok", 0), result)

    def test_setup_writers_closed_and_descriptors_unwind_on_errors(self):
        result = self.call({"op": "sandboxFDs", "workspace": str(self.workspace),
                            "session": str(self.session)})
        self.assertEqual(result["status"], "ok", result)
        self.assertEqual(result["callbacks"], 40)
        self.assertEqual(result["before"], result["after"])


if __name__ == "__main__":
    unittest.main()
