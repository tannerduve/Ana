import Harness.Adapter.ProviderIO
import Harness.Core.Policy

/-! Evaluation-only entry point: expose the same tool schemas and IO implementations
to the pinned Pi baseline. This executable does not contain an agent loop. -/
open Lean Harness

def main (args : List String) : IO UInt32 := do
  Native.installSignals
  if args == ["schemas"] then
    IO.println (toJson Coding.toolSchemas).compress
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
      outputBytes := (j.getObjValAs? Nat "outputBytes").toOption.getD 16384,
      artifacts := (j.getObjValAs? (List ArtifactRef) "artifacts").toOption.getD [] }
    let result ← match call.operation with
      | .runProcess a => ProcessIO.run context a
      | .readArtifact a =>
        try pure (.success (← ArtifactIO.read context a))
        catch e => pure (.failure e.toString)
      | _ => FilesystemIO.run context call
    let (text, error, uncertain, artifacts) := match result with
      | .success r => ((toJson r).compress, r.exitCode.any (· != 0), false, r.artifacts)
      | .failure message => (message, true, false, #[])
      | .timedOut partialResult =>
        -- This proxy uses the host profile, which cannot establish a settled sandbox timeout.
        let partialResult := partialResult.map fun (r : ToolResult) => { r with exitCode := none, sha256 := none }
        ((Json.mkObj [
          ("message", toJson "unexpected settled-timeout outcome from host evaluation tool; partial effects are uncertain"),
          ("partialResult", toJson partialResult)]).compress,
          true, true, partialResult.map ToolResult.artifacts |>.getD #[])
      | .interrupted message partialResult | .uncertain message partialResult =>
        ((Json.mkObj [("message", toJson message), ("partialResult", toJson partialResult)]).compress,
          true, true, partialResult.map ToolResult.artifacts |>.getD #[])
    IO.println (Json.mkObj [("text", toJson text), ("isError", toJson error),
      ("uncertain", toJson uncertain), ("artifacts", toJson artifacts)]).compress
    return 0
  catch _ =>
    IO.println (Json.mkObj [("text", toJson "invalid evaluation tool request"),
      ("isError", toJson true), ("uncertain", toJson false)]).compress
    return 1
