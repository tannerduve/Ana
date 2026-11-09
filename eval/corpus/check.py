#!/usr/bin/env python3
"""Independent corpus checker. Copy only fixture directories into agent mounts.

Expected answers and comparisons stay in this process. Candidate code executes
in separate processes from an allowlisted temporary source copy. This is not a
sandbox against malicious code; the enclosing evaluation runner supplies OS
isolation and excludes this checker, case data, and references from agent tools.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


class InfrastructureError(Exception):
    pass


def tool(name):
    override = os.environ.get({"lean": "LEAN_BIN", "rustc": "RUSTC_BIN", "node": "NODE_BIN"}.get(name, ""))
    found = override or shutil.which(name)
    if not found or not Path(found).is_file():
        raise InfrastructureError(f"required tool unavailable: {name}")
    return str(Path(found).resolve())


def environment():
    # Credentials, LD_PRELOAD, language startup hooks and inherited search paths
    # never enter a candidate subprocess. Required tool locations are explicit.
    return {"PATH": os.defpath, "HOME": "/nonexistent", "LANG": "C.UTF-8",
            "PYTHONDONTWRITEBYTECODE": "1"}


def worker_command(command, cwd):
    """Hide checker code, cases, references, and its parent /proc from submitted code.

    The suite opts in for every checker invocation. Local corpus development can
    still run without namespaces when this flag is absent. Only the allowlisted
    source copy is writable; compilers retain their normal output directory.
    """
    if os.environ.get("HARNESS_CHECKER_ISOLATE") != "1":
        return command
    bwrap = shutil.which("bwrap")
    if not bwrap:
        raise InfrastructureError("isolated checker requires bubblewrap")
    directory = Path(cwd).resolve()
    isolated = [bwrap, "--unshare-all", "--die-with-parent", "--new-session"]
    for path in ["/usr", "/lib", "/lib64", "/etc/alternatives", "/opt/lean", "/opt/rust", "/opt/node"]:
        if Path(path).exists():
            isolated += ["--ro-bind", path, path]
    isolated += ["--symlink", "/usr/bin", "/bin", "--dev", "/dev",
                 "--proc", "/proc", "--tmpfs", "/tmp",
                 "--bind", str(directory), str(directory), "--chdir", str(directory)]
    return isolated + command


def run(command, cwd, *, data=None, timeout=15, extra_env=None):
    try:
        result = subprocess.run(worker_command(command, cwd), cwd=cwd, input=data, text=True,
                                capture_output=True, timeout=timeout,
                                env={**environment(), **(extra_env or {})})
    except subprocess.TimeoutExpired:
        return {"timeout": True, "exit": None, "stdout": "", "stderr": ""}
    except OSError as error:
        raise InfrastructureError(f"could not launch {Path(command[0]).name}: {error}") from error
    if len(result.stdout) + len(result.stderr) > 2_000_000:
        return {"output_limit": True, "exit": result.returncode, "stdout": "", "stderr": ""}
    return {"exit": result.returncode, "stdout": result.stdout, "stderr": result.stderr}


PYTHON_WORKER = r'''
import copy, importlib.util, json, pathlib, sys
sys.path.insert(0, str(pathlib.Path(sys.argv[1]).parent))
spec=importlib.util.spec_from_file_location("candidate",sys.argv[1]);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
fn=getattr(module,sys.argv[2])
def objects(value):
    if type(value) is dict:
        return {id(value)}.union(*(objects(x) for x in value.values()))
    if type(value) is list:
        return {id(value)}.union(*(objects(x) for x in value))
    return set()
answers=[]
for case in json.load(sys.stdin):
    args=case['args']; before=copy.deepcopy(args)
    try:
        value=fn(*args)
        answer={'value':value}
        if case.get('no_alias') and objects(value)&objects(args):answer={'violation':'shared_mutable_object'}
    except ValueError:answer={'error':'ValueError'}
    except Exception as error:answer={'error':type(error).__name__}
    if args!=before:answer={'violation':'mutated_input'}
    answers.append(answer)
print(json.dumps(answers,ensure_ascii=True,separators=(',',':')))
'''

JS_WORKER = r'''
const fs=require('node:fs'); const fn=require(process.argv[1])[process.argv[2]];
function objects(value,out=new Set()) {
 if(value!==null && typeof value==='object'){if(out.has(value))return out;out.add(value);for(const x of Object.values(value))objects(x,out);}return out;
}
const answers=JSON.parse(fs.readFileSync(0,'utf8')).map(c=>{
 const before=JSON.stringify(c.args);let answer;
 try {const value=fn(...c.args);answer={value};if(c.no_alias){const ids=objects(c.args);if([...objects(value)].some(x=>ids.has(x)))answer={violation:'shared_mutable_object'};}}
 catch(e){answer={error:e.name};}
 if(before!==JSON.stringify(c.args))answer={violation:'mutated_input'};
 return answer;
});console.log(JSON.stringify(answers));
'''


def encoded(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(",", ":"))


def check_functions(task, cases, directory):
    ordinary = [(index, case) for index, case in enumerate(cases) if "args" in case]
    if not ordinary:
        return []
    payload = [{key: case[key] for key in ["args", "no_alias"] if key in case} for _, case in ordinary]
    entry = task["entry"]
    if task["language"] == "python":
        command = [sys.executable, "-I", "-S", "-c", PYTHON_WORKER, str(directory / entry["file"]), entry["function"]]
    else:
        command = [tool("node"), "--no-addons", "-e", JS_WORKER, str(directory / entry["file"]), entry["function"]]
    result = run(command, directory, data=json.dumps(payload), timeout=15)
    try:
        actual = json.loads(result["stdout"]) if result["exit"] == 0 else None
    except ValueError:
        actual = None
    if not isinstance(actual, list) or len(actual) != len(ordinary):
        return [{"kind": "candidate_process_failure", "exit": result["exit"],
                 "timeout": result.get("timeout", False)}]
    failures = []
    for (index, case), observed in zip(ordinary, actual):
        expected = {"error": case["error"]} if "error" in case else {"value": case["value"]}
        if encoded(observed) != encoded(expected):
            failures.append({"kind": "case_failure", "case": index})
    return failures


def check_cli(task, cases, directory):
    failures = []
    for index, case in enumerate(cases):
        if "cli_input" not in case:
            continue
        result = run([sys.executable, "-I", "-S", "-c",
                      "import runpy,sys;sys.path.insert(0,sys.argv[1]);p=sys.argv[2];sys.argv=sys.argv[2:];runpy.run_path(p,run_name='__main__')",
                      str(directory), str(directory / task["entry"]["cli"]), *case.get("cli_args", [])],
                     directory, data=case["cli_input"])
        valid = result["exit"] == case["exit"]
        if "cli_json" in case:
            try:
                valid &= encoded(json.loads(result["stdout"])) == encoded(case["cli_json"])
            except ValueError:
                valid = False
        if case.get("empty_stdout"):
            valid &= not result["stdout"].strip()
        if case.get("stderr"):
            valid &= bool(result["stderr"].strip())
        if not valid:
            failures.append({"kind": "cli_case_failure", "case": index})
    return failures


def check_rust(task, cases, directory):
    # The probe receives inputs only. All answers are compared outside the
    # candidate executable; no expected answer is embedded in Rust source.
    name = task["entry"]["function"]
    common = '#[path="solution.rs"] mod solution;\nuse std::io::{self,BufRead};\n'
    if task["entry"]["rust_probe"] == "tail":
        body = '''fn main(){for line in io::stdin().lock().lines(){let line=line.unwrap();let (cap,values)=line.split_once(':').unwrap();let input:Vec<i64>=if values.is_empty(){vec![]}else{values.split(',').map(|x|x.parse().unwrap()).collect()};let output=solution::tail(&input,cap.parse().unwrap());println!("{}",output.iter().map(|x|x.to_string()).collect::<Vec<_>>().join(","));}}'''
        inputs = [str(case["args"][1]) + ":" + ",".join(map(str, case["args"][0])) for case in cases]
    else:
        body = '''fn main(){for line in io::stdin().lock().lines(){let line=line.unwrap();let bytes:Vec<u8>=(0..line.len()).step_by(2).map(|i|u8::from_str_radix(&line[i..i+2],16).unwrap()).collect();let input=String::from_utf8(bytes).unwrap();match solution::FUNCTION(&input){Ok(s)=>println!("OK:{}",s.as_bytes().iter().map(|b|format!("{b:02x}")).collect::<String>()),Err(_)=>println!("ERR")}}}'''.replace("FUNCTION", name)
        inputs = [case["args"][0].encode().hex() for case in cases]
    (directory / "probe.rs").write_text(common + body)
    compiled = run([tool("rustc"), "--edition=2024", "-C", "overflow-checks=yes", "probe.rs", "-o", "probe"], directory, timeout=45)
    if compiled["exit"] != 0:
        return [{"kind": "candidate_compile_failure", "timeout": compiled.get("timeout", False)}]
    result = run([str(directory / "probe")], directory, data="\n".join(inputs) + "\n")
    actual = result["stdout"].splitlines()
    if result["exit"] != 0 or len(actual) != len(cases):
        return [{"kind": "candidate_process_failure", "exit": result["exit"]}]
    return [{"kind": "case_failure", "case": index}
            for index, (value, case) in enumerate(zip(actual, cases)) if value != case["value"]]


def check_lean(task, cases, directory):
    source = (directory / "Proof.lean").read_text()
    # Ignore line and nested block comments for the policy scan; otherwise a
    # comment saying "no sorry" would be rejected while a signature hidden in
    # a comment could satisfy the textual signature check.
    clean, index, depth = [], 0, 0
    while index < len(source):
        if source.startswith("/-", index):
            depth += 1
            index += 2
        elif depth and source.startswith("-/", index):
            depth -= 1
            index += 2
        elif depth:
            clean.append("\n" if source[index] == "\n" else " ")
            index += 1
        elif source.startswith("--", index):
            newline = source.find("\n", index)
            index = len(source) if newline < 0 else newline
        else:
            clean.append(source[index])
            index += 1
    code = "".join(clean)
    # Exact immutable signature plus an independently compiled application in
    # Spec.lean prevent weakening the statement. Compiled candidate artifacts
    # are never copied. This lexical rejection supplements actual axiom checks.
    if task["entry"]["statement"] not in code:
        return [{"kind": "theorem_statement_changed"}]
    banned = r"\b(sorry|admit|axiom|unsafe|opaque|extern|implemented_by)\b|skipKernelTC|trustLevel|#eval|#run|elab|syntax|macro"
    if re.search(banned, code):
        return [{"kind": "forbidden_proof_construct"}]
    for line in code.splitlines():
        if line.strip().startswith("import ") and line.strip() != "import Definitions":
            return [{"kind": "unexpected_proof_import"}]
    lean = tool("lean")
    for module in ["Definitions", "Proof", "Spec"]:
        result = run([lean, "-o", module + ".olean", module + ".lean"], directory,
                     timeout=25, extra_env={"LEAN_PATH": str(directory)})
        if result["exit"] != 0:
            return [{"kind": "candidate_proof_failure", "module": module,
                     "timeout": result.get("timeout", False)}]
    matches = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result["stdout"])
    clean = re.findall(r"'([^']+)' does not depend on any axioms", result["stdout"])
    theorem = task["entry"]["theorem"]
    reports = [items for name, items in matches if name == theorem]
    if theorem in clean:
        return []
    if len(reports) != 1:
        return [{"kind": "missing_axiom_report"}]
    axioms = {name.strip() for name in reports[0].split(",") if name.strip()}
    if not axioms <= set(cases[0]["allowed_axioms"]):
        return [{"kind": "unexpected_axioms", "axioms": sorted(axioms)}]
    return []


def file_bytes(workspace, relative):
    path = workspace
    for part in Path(relative).parts:
        path = path / part
        if path.is_symlink():
            raise ValueError("symlinked input")
    if not path.is_file():
        raise ValueError("missing input")
    if path.stat().st_size > 256 * 1024:
        raise ValueError("oversized input")
    return path.read_bytes()


def evaluate(task_id, workspace):
    manifest = json.loads((ROOT / "manifest.json").read_text())
    task = next((item for item in manifest["tasks"] if item["id"] == task_id), None)
    if task is None:
        raise InfrastructureError("unknown task id")
    case_bytes = (ROOT / task["cases"]).read_bytes()
    if hashlib.sha256(case_bytes).hexdigest() != task["case_sha256"]:
        raise InfrastructureError("checker case artifact changed")
    cases = json.loads(case_bytes)
    workspace = Path(workspace).absolute()
    failures, copied, hashes = [], {}, {}
    for name in task["immutable"] + task["editable"]:
        try:
            content = file_bytes(workspace, name)
        except (OSError, ValueError) as error:
            failures.append({"kind": "invalid_source", "file": name, "reason": str(error)})
            continue
        digest = hashlib.sha256(content).hexdigest()
        hashes[name] = digest
        if name in task["immutable"] and digest != task["artifact_sha256"][name]:
            failures.append({"kind": "immutable_modified", "file": name})
        copied[name] = content
    if not failures:
        with tempfile.TemporaryDirectory(prefix="corpus-independent-") as scratch:
            directory = Path(scratch)
            for name, content in copied.items():
                target = directory / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(content)
            if task["language"] in {"python", "javascript"}:
                failures += check_functions(task, cases, directory)
                failures += check_cli(task, cases, directory)
            elif task["language"] == "rust":
                failures += check_rust(task, cases, directory)
            else:
                failures += check_lean(task, cases, directory)
    return {"task_id": task_id, "split": task["split"], "passed": not failures,
            "case_count": len(cases), "immutable_count": len(task["immutable"]),
            "candidate_sha256": hashes, "failures": failures,
            "sustained_acceptance": task.get("sustained_acceptance"),
            "label": "self-authored corpus; task correctness only"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("task_id")
    parser.add_argument("workspace", type=Path)
    args = parser.parse_args()
    try:
        result = evaluate(args.task_id, args.workspace)
    except InfrastructureError as error:
        print(json.dumps({"task_id": args.task_id, "passed": False,
                          "infrastructure_error": str(error)}))
        return 2
    print(json.dumps(result, ensure_ascii=False))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
