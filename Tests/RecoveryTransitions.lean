import Harness.Core.Recovery

namespace Tests.RecoveryTransitions
open Lean Harness Harness.Recovery

private def check (label : String) (value : Bool) : IO Unit :=
  unless value do throw <| IO.userError s!"recovery transition failed: {label}"

private def failed {α : Type} : Except String α → Bool
  | .error _ => true
  | _ => false

private def pending (cursor : Cursor) : IO Cursor :=
  IO.ofExcept <| applyRecord cursor <| Json.mkObj [
    ("kind", toJson "intent"), ("id", toJson cursor.state.nextId),
    ("action", actionToJson (step cursor.state).1)]

private def complete (cursor : Cursor) (observation : Json) : IO Cursor := do
  let waiting ← pending cursor
  IO.ofExcept <| applyRecord waiting <| Json.mkObj [
    ("kind", toJson "completion"), ("id", toJson cursor.state.nextId),
    ("observation", observation)]

private def control (cursor : Cursor) : IO Cursor :=
  complete cursor (toJson ({} : ControlObservation))

private def response (calls : List RawCall) : ModelObservation :=
  .success {
    content := calls.toArray.map fun call => Json.mkObj [
      ("type", toJson "tool_use"), ("id", toJson call.id),
      ("name", toJson call.name), ("input", call.input)]
    calls, text := "", stop := .toolUse,
    usage := some {inputTokens := 10, outputTokens := 5} }

private def startCall (config : Config) (call : RawCall) : IO Cursor := do
  let initial : Cursor := {state := init "recovery-tests" config "inspect and repair the fixture"}
  let model ← control initial
  let batch ← complete model (toJson (response [call]))
  control batch

private def same (a b : State) : Bool := (toJson a).compress == (toJson b).compress

def run : IO Unit := do
  let config : Config := {
    model := "scripted", workspace := "/workspace", commands := .ask,
    compactionEnabled := false, maxModelAttempts := 8, maxToolCalls := 8, maxRetries := 2}
  let initial : Cursor := {state := init "recovery-tests" config "inspect and repair the fixture"}
  let first ← pending initial
  check "first lost control has an automatic disposition" <|
    automaticRecovery? first == some .controlLost
  let restarted ← IO.ofExcept <| applyRecord first (recoveryRecord 0 .controlLost)
  check "lost control advances identity without spending or authorizing" <|
    restarted.state.nextId == 1 && restarted.state.modelAttempts == 0 &&
    restarted.state.toolDispatches == 0 && restarted.state.grant.isNone &&
    (match (step restarted.state).1 with | .control => true | _ => false)
  check "recovery cannot consume the old position twice" <|
    failed (applyRecord restarted (recoveryRecord 0 .controlLost))

  let model ← control initial
  let modelIntent ← pending model
  let lost ← IO.ofExcept <| applyRecord modelIntent (recoveryRecord model.state.nextId .modelLost)
  check "lost inference retains reservation and records unknown usage" <|
    lost.state.modelAttempts == 1 && lost.state.unknownUsage == 1 &&
    lost.state.retryCount == 1 && lost.state.nextId == model.state.nextId + 1 &&
    (match lost.state.phase with | .waiting 1000 => true | _ => false)
  let waitIntent ← pending lost
  let waitedAgain ← IO.ofExcept <| applyRecord waitIntent (recoveryRecord lost.state.nextId .waitLost)
  check "lost delay is restarted under a fresh identity" <|
    waitedAgain.state.nextId == lost.state.nextId + 1 &&
    waitedAgain.state.modelAttempts == 1 && waitedAgain.state.unknownUsage == 1 &&
    (match waitedAgain.state.phase with | .waiting 1000 => true | _ => false)
  let elapsed ← complete waitedAgain (toJson WaitObservation.elapsed)
  let secondModel ← control elapsed
  check "new inference uses a new identity and reservation" <|
    secondModel.state.nextId > model.state.nextId && secondModel.state.modelAttempts == 2 &&
    (match (step secondModel.state).1 with | .model _ => true | _ => false)
  let noRetries : Cursor := {state := init "no-retries" {config with maxRetries := 0} "task"}
  let noRetryModel ← control noRetries
  let noRetryIntent ← pending noRetryModel
  let stoppedModel ← IO.ofExcept <| recover noRetryIntent noRetryModel.state.nextId .modelLost
  check "lost model obeys frozen retry policy" <|
    stoppedModel.state.modelAttempts == 1 && stoppedModel.state.unknownUsage == 1 &&
    (match (step stoppedModel.state).1 with | .finish (.failure _) => true | _ => false)

  let process : RawCall := {id := "p", name := "process", input := Json.mkObj [("argv", toJson #["/bin/true"])]}
  let ask ← startCall config process
  let askIntent ← pending ask
  let askAgain ← IO.ofExcept <| applyRecord askIntent (recoveryRecord ask.state.nextId .approvalLost)
  check "lost approval cannot manufacture a grant or spend a tool reservation" <|
    askAgain.state.grant.isNone && askAgain.state.toolDispatches == 0 &&
    askAgain.state.nextId == ask.state.nextId + 1
  let freshAsk ← control askAgain
  check "interrupted approval is asked again" <|
    match (step freshAsk.state).1 with | .ask _ => true | _ => false
  let approved ← complete freshAsk (toJson ApprovalObservation.approved)
  let approvedControl ← pending approved
  let invalidated ← IO.ofExcept <| recover approvedControl approved.state.nextId .controlLost
  check "restart invalidates a previously granted but undispatched approval" <|
    invalidated.state.grant.isNone && invalidated.state.toolDispatches == 0
  let reapproval ← control invalidated
  check "approval invalidation leads to another ask" <|
    match (step reapproval.state).1 with | .ask _ => true | _ => false

  let read : RawCall := {id := "r", name := "read", input := Json.mkObj [("path", toJson "file.txt")]}
  let tool ← startCall config read
  let readIntent ← pending tool
  let recoveredRead ← IO.ofExcept <| applyRecord readIntent (recoveryRecord tool.state.nextId .readLost)
  check "unknown read settles once without another dispatch reservation" <|
    recoveredRead.state.toolDispatches == 1 && recoveredRead.state.modelAttempts == 1 &&
    recoveredRead.state.nextId == tool.state.nextId + 1 &&
    historyValid recoveredRead.state.history && recoveredRead.state.seenCallIds == ["r"]
  let unknown ← complete tool (toJson (ToolObservation.uncertain "read interrupted" : ToolObservation ToolResult))
  let terminal ← match (step unknown.state).1 with
    | .finish outcome => IO.ofExcept <| applyRecord unknown <| Json.mkObj [
        ("kind", toJson "terminal"), ("id", toJson unknown.state.nextId), ("outcome", toJson outcome)]
    | _ => throw <| IO.userError "uncertain read did not stop"
  let readSettled ← IO.ofExcept <| applyRecord terminal (recoveryRecord tool.state.nextId .readLost)
  check "suspended read settles through its saved queue after a recovery stop" <|
    same readSettled.state recoveredRead.state && !readSettled.terminal && readSettled.suspended.isNone
  let ref : ArtifactRef := {
    id := "a-" ++ String.ofList (List.replicate 64 'a'),
    sha256 := String.ofList (List.replicate 64 'b'), label := "output",
    storedBytes := 10, totalBytes := 20, truncated := true }
  let partialCursor ← complete tool (toJson (ToolObservation.uncertain "read interrupted"
    (some {text := "partial contents", artifacts := #[ref]}) : ToolObservation ToolResult))
  let partialSettled ← IO.ofExcept <| recover partialCursor tool.state.nextId .readLost
  check "settling an uncertain call preserves its accepted partial artifacts" <|
    partialCursor.state.artifacts == [ref] && partialSettled.state.artifacts == [ref] &&
    partialSettled.state.toolDispatches == 1 && historyValid partialSettled.state.history
  let invalidArtifact ← complete tool (toJson (ToolObservation.success {
    text := "completed read", exitCode := some 0, artifacts := #[{ref with id := "invalid"}] } : ToolObservation ToolResult))
  check "artifact rejection does not erase a known completed outcome or invent uncertainty" <|
    invalidArtifact.suspended.isNone && invalidArtifact.state.artifacts.isEmpty &&
    invalidArtifact.state.toolDispatches == 1 && historyValid invalidArtifact.state.history &&
    (match invalidArtifact.state.phase with | .controlTools [] => true | _ => false)

  let create : RawCall := {id := "c", name := "create", input := Json.mkObj [
    ("path", toJson "new.txt"), ("content", toJson "intended content")]}
  let creating ← startCall config create
  let createIntent ← pending creating
  check "create has no automatic retry or fabricated read settlement" <|
    (automaticRecovery? createIntent).isNone &&
    failed (recover createIntent creating.state.nextId .readLost)
  let abandoned ← IO.ofExcept <| applyRecord createIntent <|
    recoveryRecord creating.state.nextId (.mutationAbandoned "inspect the current file before further work")
  check "create abandonment retains the reservation and pairs its admitted call" <|
    abandoned.state.toolDispatches == 1 && abandoned.state.modelAttempts == 1 &&
    historyValid abandoned.state.history && abandoned.state.seenCallIds == ["c"] &&
    abandoned.state.nextId == creating.state.nextId + 1
  check "empty abandonment note is rejected" <|
    failed (recover createIntent creating.state.nextId (.mutationAbandoned "  "))
  check "wrong operation identity is rejected" <|
    failed (recover createIntent (creating.state.nextId + 1) (.mutationAbandoned "checked"))
  let wrongSource : RecoveryRecord := {
    disposition := .mutationAbandoned "checked", provenance := .automatic }
  check "automatic provenance cannot authorize mutation abandonment" <|
    failed (applyRecord createIntent <| Json.mkObj [("kind", toJson "recovery"),
      ("id", toJson creating.state.nextId), ("recovery", toJson wrongSource)])
  let futureRecord : RecoveryRecord := {version := 2, disposition := .readLost, provenance := .automatic}
  check "unsupported recovery record versions are rejected" <|
    failed (applyRecord readIntent <| Json.mkObj [("kind", toJson "recovery"),
      ("id", toJson tool.state.nextId), ("recovery", toJson futureRecord)])
  let allowedProcess ← startCall {config with commands := .allow} process
  let processIntent ← pending allowedProcess
  check "file abandonment cannot bypass process settled-resource assertion" <|
    failed (recover processIntent allowedProcess.state.nextId (.mutationAbandoned "checked"))
  let hardStop : Cursor := {state := stop tool.state .cancelled, terminal := true, suspended := some tool.state}
  check "ordinary terminals refuse recovery even with a supplied suspended position" <|
    failed (recover hardStop tool.state.nextId .readLost) &&
    failed (resolve hardStop tool.state.nextId (.processCompleted 0 "checked"))

  let compacting ← startCall {config with
    compactionEnabled := true, compactAtPercent := 1,
    maxContextBytes := 100000, compactionKeepMessages := 2} read
  let result ← complete compacting (toJson (ToolObservation.success {text := "contents"} : ToolObservation ToolResult))
  let emptyBatch ← control result
  let summary ← control emptyBatch
  check "fixture reaches a real summary admission" <|
    match (step summary.state).1 with | .model request => request.purpose == .summary | _ => false
  let summaryIntent ← pending summary
  let summaryLost ← IO.ofExcept <| recover summaryIntent summary.state.nextId .modelLost
  check "lost summary preserves raw history, view, source and reserved attempts" <|
    (toJson summaryLost.state.history).compress == (toJson summary.state.history).compress &&
    (toJson summaryLost.state.activeView).compress == (toJson summary.state.activeView).compress &&
    (toJson summaryLost.state.pendingSummary).compress == (toJson summary.state.pendingSummary).compress &&
    summaryLost.state.modelAttempts == summary.state.modelAttempts && summaryLost.state.unknownUsage == 1
  IO.println "recovery transitions: lost observations, exact approvals, mutation abandonment and replay checks passed"

end Tests.RecoveryTransitions
