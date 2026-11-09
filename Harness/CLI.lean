import Harness.Runner

open Lean Harness

private def usage : String := "harness run --workspace PATH --config CONFIG --task TEXT [--session PATH] [--json] [--script FILE]\nharness resume SESSION [--json]\nharness inspect SESSION\nharness replay SESSION\nharness cancel SESSION"

private def value (args : List String) (key : String) : Option String :=
  match args with
  | "--json" :: tail => value tail key
  | a :: b :: tail => if a == key then some b else value tail key
  | _ => none

private def hasEvents : List String → Bool
  | [] => false
  | "--json" :: _ => true
  | _ :: _ :: tail => hasEvents tail
  | _ => false

private def required (args : List String) (key : String) : IO String :=
  match value args key with
  | some v => pure v
  | none => throw <| IO.userError s!"missing {key}"

private def parseOptions : List String → Except String Unit
  | [] => .ok ()
  | "--json" :: tail => parseOptions tail
  | flag :: _value :: tail =>
    if ["--workspace", "--config", "--task", "--session", "--script"].contains flag
    then parseOptions tail else .error s!"unknown option: {flag}"
  | [flag] => .error s!"missing value or unknown option: {flag}"

private def readJson (path : String) : IO Json := do
  IO.ofExcept <| Json.parse (← IO.FS.readFile path)

private def absolute (p : String) : IO String := do
  if (System.FilePath.mk p).isAbsolute then return p
  return ((← IO.currentDir) / p).toString

private def defaultSession (identity : String) : IO String := do
  let root ← match ← IO.getEnv "XDG_STATE_HOME" with
    | some path =>
      if (System.FilePath.mk path).isAbsolute then pure (System.FilePath.mk path)
      else homeState
    | none => homeState
  return (root / "lean-harness" / "sessions" / identity).toString
where
  homeState : IO System.FilePath := do
    let some homePath ← IO.getEnv "HOME"
      | throw <| IO.userError "HOME or absolute XDG_STATE_HOME is required; alternatively provide --session"
    unless (System.FilePath.mk homePath).isAbsolute do
      throw <| IO.userError "HOME must be absolute; alternatively provide --session"
    return System.FilePath.mk homePath / ".local" / "state"

private def runCLI (args : List String) : IO UInt32 := do
  match args with
  | [] | ["--help"] | ["help"] => IO.println usage; return 0
  | "run" :: options =>
    IO.ofExcept (parseOptions options)
    let workspace ← IO.FS.realPath (← required options "--workspace")
    let raw ← readJson (← required options "--config")
    let fields ← IO.ofExcept raw.getObj?
    let model ← IO.ofExcept (raw.getObjValAs? String "model")
    let defaults : Config := {model, workspace := workspace.toString}
    let known ← IO.ofExcept (toJson defaults).getObj?
    for (key, _) in fields.toList do
      unless known.contains key do throw <| IO.userError s!"unknown configuration field: {key}"
    let config : Config ← IO.ofExcept <| fromJson? ((toJson defaults).mergeObj raw)
    let config := {config with workspace := workspace.toString}
    if config.model.isEmpty || config.operationTimeoutMs == 0 || config.maxElapsedMs == 0 then
      throw <| IO.userError "model and positive operation/session time limits are required"
    let task ← required options "--task"
    let id ← IO.monoNanosNow
    let session ← match value options "--session" with
      | some path => absolute path
      | none => defaultSession s!"{id}"
    let script ← match value options "--script" with
      | none => pure none
      | some path => do
        let raw ← readJson path
        pure (some (← IO.ofExcept raw.getArr?))
    Runner.start {session, script, events := hasEvents options} config task
  | cmd :: session :: options =>
    IO.ofExcept (parseOptions options)
    let session ← absolute session
    let o : Runner.Options := {session, events := hasEvents options}
    match cmd with
    | "inspect" | "replay" => Runner.inspect o
    | "resume" => Runner.resume o
    | "cancel" =>
      unless ← (System.FilePath.mk session / "journal.jsonl").pathExists do
        throw <| IO.userError "unknown session"
      IO.FS.writeFile (session ++ "/cancel") "cancel\n"
      return 0
    | _ => throw <| IO.userError usage
  | _ => throw <| IO.userError usage

def main (args : List String) : IO UInt32 := do
  try
    Native.installSignals
    runCLI args
  catch e =>
    (← IO.getStderr).putStrLn s!"harness: {e}"
    return 2
