import Harness.Core.Policy
import Harness.Adapter.JournalIO
import Harness.Adapter.ProviderIO
import Harness.Adapter.ApprovalIO
import Tests.NativeABI

/-! Test-only JSON entry point for exercising the real Lean IO functions.
The production executable calls these functions directly, without this protocol. -/
open Lean Harness

private def str (j : Json) (key : String) (fallback := "") : String :=
  (j.getObjValAs? String key).toOption.getD fallback
private def nat (j : Json) (key : String) (fallback : Nat) : Nat :=
  (j.getObjValAs? Nat key).toOption.getD fallback

private def toolJson : ToolObservation ToolResult → Json
  | .success r => Json.mkObj <| [("status", toJson "ok"), ("text", toJson r.text),
      ("truncated", toJson (r.artifact.isSome))] ++
      (r.exitCode.toList.map fun x => ("exitCode", toJson x)) ++
      (r.artifact.toList.map fun x => ("artifact", toJson x)) ++
      (r.sha256.toList.map fun x => ("sha256", toJson x))
  | .failure message => Json.mkObj [("status", toJson "failed"), ("text", toJson message)]
  | .interrupted message => Json.mkObj [("status", toJson "interrupted"), ("text", toJson message)]
  | .uncertain message => Json.mkObj [("status", toJson "uncertain"), ("text", toJson message)]

private def dispatch (j : Json) : IO Json := do
  match str j "op" with
  | "nativeAbi" => Tests.NativeABI.run j
  | "tool" =>
    let raw ← IO.ofExcept (j.getObjVal? "call")
    let args ← IO.ofExcept (raw.getObjVal? "args")
    let call ← IO.ofExcept <| decodeCall {id := "contract", name := str raw "name", input := args}
    let context : ToolContext := {
      workspace := str j "workspace"
      timeoutMs := nat j "timeoutMs" 30000
      outputBytes := nat j "outputBytes" 65536
      artifactDir := str j "artifactDir"
      cancelPath := str j "cancelPath"}
    let result ← match call.operation with
      | .runProcess args => ProcessIO.run context args
      | _ => FilesystemIO.run context call
    return toolJson result
  | "approval" =>
    let answer ← ApprovalIO.ask (nat j "timeoutMs" 30000) (str j "cancelPath")
    return Json.mkObj [("status", toJson (match answer with | .interrupted => "interrupted" | _ => "ok")),
      ("approved", toJson (match answer with | .approved => true | _ => false))]
  | "http" =>
    let payload ← IO.ofExcept (j.getObjVal? "payload")
    let result ← ProviderIO.transport payload {
      timeoutMs := nat j "timeoutMs" 60000
      responseBytes := nat j "responseBytes" 2000000
      cancelPath := str j "cancelPath"
      endpoint := str j "endpoint" "https://api.anthropic.com/v1/messages"}
    return match result with
    | .complete status body => Json.mkObj [("status", toJson "ok"), ("httpStatus", toJson status), ("body", toJson body)]
    | .failure _ message => Json.mkObj [("status", toJson "failed"), ("error", toJson message)]
    | .interrupted => Json.mkObj [("status", toJson "interrupted")]
    | .uncertain message => Json.mkObj [("status", toJson "uncertain"), ("error", toJson message)]
  | "capture" =>
    let args ← IO.ofExcept (j.getObjValAs? (Array String) "args")
    let result ← ProcessIO.capture {
      cmd := str j "cmd"
      args := args
      input := (str j "input").toUTF8
      timeoutMs := nat j "timeoutMs" 30000
      cancelPath := str j "cancelPath"
      stdoutBytes := nat j "stdoutBytes" 65536
      stderrBytes := nat j "stderrBytes" 65536}
    return Json.mkObj [("status", toJson (match result.status with
        | .completed => "ok" | .failedToStart => "failed" | .interrupted => "interrupted" | .uncertain => "uncertain")),
      ("stdout", toJson (String.fromUTF8! result.stdout)), ("stderr", toJson (String.fromUTF8! result.stderr)),
      ("stdoutTotal", toJson result.stdoutTotal), ("stderrTotal", toJson result.stderrTotal),
      ("exitCode", toJson (result.exitCode.map UInt32.toNat))]
  | "journalRead" =>
    return (toJson (← JournalIO.read (str j "path"))).mergeObj (Json.mkObj [("status", toJson "ok")])
  | "journalAppend" =>
    let path := str j "path"
    IO.FS.createDirAll ((System.FilePath.mk path).parent.getD ".")
    JournalIO.append path (← IO.ofExcept (j.getObjVal? "record"))
    return Json.mkObj [("status", toJson "ok")]
  | "sessionCreate" =>
    JournalIO.createSession (str j "path")
    return Json.mkObj [("status", toJson "ok")]
  | _ => throw <| IO.userError "unknown contract test operation"

def main : IO Unit := do
  Native.installSignals
  let result ← try
      dispatch (← IO.ofExcept (Json.parse (← (← IO.getStdin).getLine)))
    catch e => pure <| Json.mkObj [("status", toJson "failed"), ("text", toJson e.toString), ("error", toJson e.toString)]
  IO.println result.compress
