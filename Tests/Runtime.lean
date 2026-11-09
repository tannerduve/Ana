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
      ("truncated", toJson (!r.artifacts.isEmpty)), ("artifacts", toJson r.artifacts)] ++
      (r.exitCode.toList.map fun x => ("exitCode", toJson x)) ++
      (r.sha256.toList.map fun x => ("sha256", toJson x))
  | .failure message => Json.mkObj [("status", toJson "failed"), ("text", toJson message)]
  | .interrupted message partialResult => Json.mkObj [("status", toJson "interrupted"), ("text", toJson message), ("partialResult", toJson partialResult)]
  | .uncertain message partialResult => Json.mkObj [("status", toJson "uncertain"), ("text", toJson message), ("partialResult", toJson partialResult)]
  | .timedOut partialResult => Json.mkObj [("status", toJson "timedOut"), ("partialResult", toJson partialResult)]

private def dispatch (j : Json) : IO Json := do
  let invocationDeadlineMs : Option Nat ← match (j.getObjValAs? Nat "invocationBudgetMs").toOption with
    | none => pure none
    | some budget => do
      let now ← IO.monoMsNow
      pure (some (now + budget))
  match str j "op" with
  | "sandboxValidate" =>
    ProcessIO.validateSandbox (str j "workspace") (str j "session") .bubblewrap
      ((j.getObjValAs? (Array String) "toolchainRoots").toOption.getD #[]) (nat j "timeoutMs" 5000)
    return Json.mkObj [("status", toJson "ok")]
  | "nativeAbi" => Tests.NativeABI.run j
  | "sandboxFDs" =>
    let context : ToolContext := {
      workspace := str j "workspace", artifactDir := str j "session" ++ "/artifacts",
      timeoutMs := 3000, outputBytes := 4096, cancelPath := "", executionProfile := .bubblewrap}
    let before := (← (System.FilePath.mk "/proc/self/fd").readDir).size
    let mut callbacks := 0
    for _ in [:40] do
      let (reader, writer) ← Native.statusPipe
      Native.withFD (pure reader) fun _ => Native.withFD (pure writer) fun _ => do
        try
          Sandbox.withPlan context {argv := #["/usr/bin/true"]} writer fun plan => do
            for (index, expected) in [(4, "127.0.0.1 localhost\n::1 localhost\n"), (5, "hosts: files\n")] do
              let fd := plan.inherited[index]!
              let bytes ← Native.readAvailable fd 512
              unless bytes == some expected.toUTF8 do throw <| IO.userError "setup data bytes differ"
              unless (← Native.readAvailable fd 512) == some ByteArray.empty do
                throw <| IO.userError "setup writer remained open at callback"
            (throw <| IO.userError "intentional callback failure" : IO Unit)
        catch error =>
          unless (toString error).contains "intentional callback failure" do throw error
        try
          Sandbox.withPlan context {argv := #["/usr/bin/true"], cwd := "missing-directory"} writer fun _ =>
            (throw <| IO.userError "missing directory unexpectedly admitted" : IO Unit)
        catch error =>
          if (toString error).contains "missing directory unexpectedly admitted" then throw error
      callbacks := callbacks + 1
    let after := (← (System.FilePath.mk "/proc/self/fd").readDir).size
    unless before == after do throw <| IO.userError "setup descriptors leaked after failure"
    return Json.mkObj [("status", toJson "ok"), ("before", toJson before),
      ("after", toJson after), ("callbacks", toJson callbacks)]
  | "tool" =>
    let raw ← IO.ofExcept (j.getObjVal? "call")
    let args ← IO.ofExcept (raw.getObjVal? "args")
    let call ← IO.ofExcept <| decodeCall {id := "contract", name := str raw "name", input := args}
    let context : ToolContext := {
      workspace := str j "workspace"
      timeoutMs := nat j "timeoutMs" 30000
      invocationDeadlineMs
      localDeadline := (j.getObjValAs? Bool "localDeadline").toOption.getD false
      outputBytes := nat j "outputBytes" 65536
      artifactDir := str j "artifactDir"
      cancelPath := str j "cancelPath"
      executionProfile := (j.getObjValAs? ExecutionProfile "executionProfile").toOption.getD .host
      toolchainRoots := (j.getObjValAs? (Array String) "toolchainRoots").toOption.getD #[]
      maxArtifactBytes := nat j "maxArtifactBytes" (16 * 1024 * 1024)
      maxSessionArtifactBytes := nat j "maxSessionArtifactBytes" (64 * 1024 * 1024)
      artifacts := (j.getObjValAs? (List ArtifactRef) "artifacts").toOption.getD []}
    let result ← match call.operation with
      | .runProcess args => ProcessIO.run context args
      | _ => FilesystemIO.run context call
    return toolJson result
  | "approval" =>
    let answer ← ApprovalIO.ask (nat j "timeoutMs" 30000) (str j "cancelPath")
    return Json.mkObj [("status", toJson (match answer with | .interrupted => "interrupted" | _ => "ok")),
      ("approved", toJson (match answer with | .approved => true | _ => false))]
  | "modelStream" =>
    let progress ← IO.mkRef (#[] : Array String)
    let emit := (j.getObjValAs? Bool "emitProgress").toOption.getD false
    let result ← ProviderIO.request {
      model := "fixture-model", system := "fixture", messages := [], maxTokens := 128 } {
      timeoutMs := nat j "timeoutMs" 3000
      invocationDeadlineMs
      responseBytes := nat j "responseBytes" 2000000
      cancelPath := str j "cancelPath"
      endpoint := str j "endpoint" } (fun text => do
        progress.modify (·.push text)
        if emit then
          let stdout ← IO.getStdout
          stdout.putStrLn ((Json.mkObj [("provisional", toJson text)]).compress)
          stdout.flush)
    return Json.mkObj [("observation", toJson result), ("progress", toJson (← progress.get))]
  | "http" =>
    let payload ← IO.ofExcept (j.getObjVal? "payload")
    let result ← ProviderIO.transport payload {
      timeoutMs := nat j "timeoutMs" 60000
      invocationDeadlineMs
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
      invocationDeadlineMs
      cancelPath := str j "cancelPath"
      stdoutBytes := nat j "stdoutBytes" 65536
      stderrBytes := nat j "stderrBytes" 65536}
    return Json.mkObj [("status", toJson (match result.status with
        | .completed => "ok" | .failedToStart => "failed" | .interrupted => "interrupted" | .uncertain => "uncertain" | .timedOut => "timedOut")),
      ("stdout", toJson (String.fromUTF8! result.stdout)), ("stderr", toJson (String.fromUTF8! result.stderr)),
      ("stdoutTotal", toJson result.stdoutTotal), ("stderrTotal", toJson result.stderrTotal),
      ("exitCode", toJson (result.exitCode.map UInt32.toNat))]
  | "journalRead" =>
    return (toJson (← JournalIO.read (str j "path"))).mergeObj (Json.mkObj [("status", toJson "ok")])
  | "journalReadSummary" =>
    let result ← JournalIO.read (str j "path")
    return Json.mkObj [("status", toJson "ok"), ("records", toJson result.records.size),
      ("checksum", toJson result.checksum), ("interrupted", toJson result.interrupted)]
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
