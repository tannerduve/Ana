"""Negative control: submitted code cannot read hidden checker data at runtime."""
import json
from pathlib import Path
import shutil
import socket
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "runner"))
from suite import sandbox, environment, checker


class EvaluationIsolation(unittest.TestCase):
    def test_isolated_checker_accepts_references_and_rejects_baselines(self):
        corpus = ROOT / "corpus"
        manifest = json.loads((corpus / "manifest.json").read_text())
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for task in manifest["tasks"]:
                with self.subTest(task=task["id"]):
                    output = root / task["id"]
                    output.mkdir()
                    workspace = output / "workspace"
                    shutil.copytree(corpus / task["fixture"], workspace)
                    baseline = checker(task, workspace, output, "baseline")
                    self.assertNotIn("infrastructure_error", baseline)
                    self.assertFalse(baseline["passed"])
                    # Mechanical positive control only: do not inspect or tune
                    # against reserved cases or reference implementations.
                    for name in task["editable"]:
                        shutil.copyfile(corpus / task["reference"] / name, workspace / name)
                    reference = checker(task, workspace, output, "reference")
                    self.assertNotIn("infrastructure_error", reference)
                    self.assertTrue(reference["passed"], reference)

    def test_candidate_runtime_cannot_read_checker_cases_or_references(self):
        with tempfile.TemporaryDirectory() as temporary, socket.socket() as listener:
            root = Path(temporary)
            workspace = root / "candidate"
            workspace.mkdir()
            checker = root / "checker"
            (checker / "cases").mkdir(parents=True)
            (checker / "references").mkdir()
            (checker / "cases" / "sentinel.json").write_text('"hidden expected answer"')
            (checker / "references" / "answer.py").write_text("hidden reference implementation")
            shutil.copyfile(ROOT / "corpus/check.py", checker / "check.py")
            (checker / "controller.py").write_text(
                "import json, pathlib, sys, check\n"
                "print(json.dumps(check.run([sys.executable, '/workspace/probe.py'], "
                "pathlib.Path('/workspace'))))\n")
            listener.bind(("127.0.0.1", 0))
            listener.listen()
            port = listener.getsockname()[1]
            (workspace / "probe.py").write_text(
                "import json,pathlib,socket\n"
                "results={}\n"
                "for name,path in [('cases','/checker/cases/sentinel.json'),"
                "('reference','/checker/references/answer.py')]:\n"
                " try: results[name]=pathlib.Path(path).read_text()\n"
                " except OSError: results[name]=None\n"
                "try:\n"
                f" connection=socket.create_connection(('127.0.0.1',{port}),timeout=1)\n"
                " connection.close();results['host_network']=True\n"
                "except OSError: results['host_network']=False\n"
                "pathlib.Path('worker-output').write_text('compiler output remains writable')\n"
                "print(json.dumps(results))\n")

            observations = {}
            for isolated in [False, True]:
                env = environment()
                if isolated:
                    env["HARNESS_CHECKER_ISOLATE"] = "1"
                result = subprocess.run(
                    sandbox(workspace, [(checker, "/checker", False)]) +
                    ["/usr/bin/python3", "/checker/controller.py"], env=env,
                    capture_output=True, text=True, timeout=20)
                self.assertEqual(result.returncode, 0, result.stderr)
                report = json.loads(result.stdout)
                self.assertEqual(report["exit"], 0, report)
                observations[isolated] = json.loads(report["stdout"])
                self.assertEqual((workspace / "worker-output").read_text(),
                                 "compiler output remains writable")

            # The first run proves this fixture exposes the original vulnerability.
            self.assertEqual(observations[False]["cases"], '"hidden expected answer"')
            self.assertEqual(observations[False]["reference"], "hidden reference implementation")
            self.assertTrue(observations[False]["host_network"])
            self.assertIsNone(observations[True]["cases"])
            self.assertIsNone(observations[True]["reference"])
            self.assertFalse(observations[True]["host_network"])


if __name__ == "__main__":
    unittest.main()
