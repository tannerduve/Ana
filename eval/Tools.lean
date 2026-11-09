import Harness.Adapter.ProviderIO
import Harness.Core.Policy

/-! Evaluation-only entry point: expose the same tool schemas and IO implementations
to the pinned Pi baseline. This executable does not contain an agent loop. -/
open Lean Harness

def main (args : List String) : IO UInt32 := do
  Native.installSignals
  if args == ["schemas"] then
    IO.println (toJson Provider.toolSchemas).compress
    return 0
  try
    let j ← IO.ofExcept <| Json.parse (← (← IO.getStdin).getLine)
    let get (key : String) : IO String := IO.ofExcept (j.getObjValAs? String key)
    let raw ← IO.ofExcept (j.getObjValAs? RawCall "call")
    let call ← IO.ofExcept (decodeCall raw)
    let context : ToolContext := {
      workspace := ← get "workspace", artifactDir := ← get "artifactDir",
      cancelPath := ← get "cancelPath",
      timeoutMs := (j.getObjValAs? Nat "timeoutMs").toOption.getD 60000,
      outputBytes := (j.getObjValAs? Nat "outputBytes").toOption.getD 16384 }
    let result ← match call.operation with
      | .runProcess a => ProcessIO.run context a
      | _ => FilesystemIO.run context call
    let (text, error, uncertain) := match result with
      | .success r => ((toJson r).compress, r.exitCode.any (· != 0), false)
      | .failure message => (message, true, false)
      | .interrupted message | .uncertain message => (message, true, true)
    IO.println (Json.mkObj [("text", toJson text), ("isError", toJson error),
      ("uncertain", toJson uncertain)]).compress
    return 0
  catch _ =>
    IO.println (Json.mkObj [("text", toJson "invalid evaluation tool request"),
      ("isError", toJson true), ("uncertain", toJson false)]).compress
    return 1
