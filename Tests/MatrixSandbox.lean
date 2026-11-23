import Harness.Adapter.ProcessIO

open Harness

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def run (root : System.FilePath) : IO Unit := do
  let workspace := root / "workspace"
  let session := root / "session"
  let skills := root / "skills"
  let scratch := root / "scratch"
  for directory in [workspace, session / "artifacts", skills, scratch] do IO.FS.createDirAll directory
  IO.FS.writeFile (workspace / "source.txt") "original"
  IO.FS.writeFile (skills / "skill.txt") "selected skill"
  IO.FS.writeFile (root / "private.txt") "private session data"
  ProcessIO.validateSandbox workspace.toString session.toString .bubblewrap #[]
  let context : ToolContext := {
    workspace := workspace.toString, sessionPath := session.toString,
    timeoutMs := 10000, outputBytes := 4096, artifactDir := (session / "artifacts").toString,
    cancelPath := "", executionProfile := .bubblewrap, workspaceReadOnly := true,
    resourceMounts := #[{name := "skills", path := skills.toString},
      {name := "scratch", path := scratch.toString, readOnly := false}]}
  let script := "import os, pathlib, sys\n" ++
    "root = pathlib.Path(sys.argv[1])\n" ++
    "assert (root / 'source.txt').read_text() == 'original'\n" ++
    "for path in [root / 'changed.txt', pathlib.Path('/workspace/changed.txt'), pathlib.Path('/opt/harness/resources/skills/changed.txt')]:\n" ++
    "  try:\n" ++
    "    path.write_text('forbidden')\n" ++
    "  except OSError:\n" ++
    "    pass\n" ++
    "  else:\n" ++
    "    raise AssertionError('read-only mount accepted a write: ' + str(path))\n" ++
    "assert pathlib.Path('/opt/harness/resources/skills/skill.txt').read_text() == 'selected skill'\n" ++
    "pathlib.Path('/opt/harness/resources/scratch/result.txt').write_text('experiment')\n" ++
    "assert not pathlib.Path(sys.argv[2]).exists()\n" ++
    "assert os.environ.get('HOME') == '/tmp/home'\n" ++
    "assert not any(key in os.environ for key in ['ANTHROPIC_API_KEY', 'OPENAI_API_KEY', 'MATRIX_AGENT_SETTINGS'])\n"
  let result ← ProcessIO.run context {argv := #["/usr/bin/python3", "-c", script,
    workspace.toString, (root / "private.txt").toString]}
  match result with
  | .success value => check (value.exitCode == some 0) s!"scoped sandbox failed: {value.text}"
  | _ => throw <| IO.userError "scoped sandbox did not complete"
  check ((← IO.FS.readFile (scratch / "result.txt")) == "experiment") "scratch result was not retained"
  check (!(← (workspace / "changed.txt").pathExists)) "workspace was modified through an alias"
  check (!(← (skills / "changed.txt").pathExists)) "selected skills were modified"
  let host ← ProcessIO.run {context with executionProfile := .host}
    {argv := #["/usr/bin/touch", "host-escape"]}
  match host with
  | .failure _ => pure ()
  | _ => throw <| IO.userError "scoped process silently used host execution"
  check (!(← (workspace / "host-escape").pathExists)) "host process escaped its role scope"
  let invalid ← ProcessIO.run {context with resourceMounts := #[{name := "escape", path := root.toString}]}
    {argv := #["/usr/bin/touch", "mount-escape"]}
  match invalid with
  | .success _ => throw <| IO.userError "resource containing session storage was mounted"
  | _ => pure ()
  check (!(← (workspace / "mount-escape").pathExists)) "invalid resource mount executed its process"

def main : IO Unit := do
  let identity ← IO.monoNanosNow
  let root := System.FilePath.mk s!"/tmp/ana-matrix-sandbox-{identity}"
  IO.FS.createDir root
  try
    run root
    IO.println "Matrix sandbox contracts passed"
  finally
    IO.FS.removeDirAll root
