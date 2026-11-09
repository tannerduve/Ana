import Tests.Core
import Harness.Core.Recovery

/-! Actual step/replay tests for a settled process timeout, including a queued
mutation that must not dispatch, partial metadata, cancellation and forged scope. -/
namespace Tests.SettledTimeout
open Harness Harness.Recovery Lean Tests.Core

private def config : Config :=
  {cfg with commands := .allow, executionProfile := .bubblewrap, compactionEnabled := false}

private def suffix : RawCall := raw "later-create" "create" <| toJson
  ({path := "must-not-run.txt", content := "no"} : CreateArgs)

private def proposal : ModelObservation := .success {
  content := #[callBlock processCall, callBlock suffix], calls := [processCall, suffix],
  text := "", stop := .toolUse, usage := some {inputTokens := 11, outputTokens := 7}}

private def intent (state : State) : Json := Json.mkObj [
  ("kind", toJson "intent"), ("id", toJson state.nextId),
  ("action", actionToJson (step state).1)]

private def completion (state : State) (observation : Json) : Json := Json.mkObj [
  ("kind", toJson "completion"), ("id", toJson state.nextId), ("observation", observation)]

private def complete (cursor : Cursor) (observation : Json) : IO Cursor := do
  let waiting ← IO.ofExcept <| applyRecord cursor (intent cursor.state)
  IO.ofExcept <| applyRecord waiting (completion cursor.state observation)

private def resultBlocks (state : State) : Array Json :=
  (state.history.getLast?.map (·.content)).getD #[]

def run : IO Unit := do
  let initial := init "settled-timeout" config "inspect and test"
  expect (initial.schemaVersion == sessionSchemaVersion) "application-indexed session has the wrong schema"
  let modeled ← complete {state := initial} (toJson ({} : ControlObservation))
  let queued ← complete modeled (toJson proposal)
  let launched ← complete queued (toJson ({} : ControlObservation))
  let (call, remaining) ← match launched.state.phase with
    | .tool call remaining => pure (call, remaining)
    | _ => throw <| IO.userError "fixture did not emit process"
  expect (remaining.map (·.id) == [suffix.id] && launched.state.toolDispatches == 1)
    "fixture queue or dispatch reservation is wrong"
  let artifact : ArtifactRef := {
    id := "a-" ++ String.ofList (List.replicate 64 '1')
    sha256 := String.ofList (List.replicate 64 'a')
    label := "stdout", storedBytes := 3, totalBytes := 9, truncated := true}
  let partialResult : ToolResult := {
    text := "partial output", exitCode := some 143
    sha256 := some (String.ofList (List.replicate 64 'b')), artifacts := #[artifact]}
  let observation : ToolObservation ToolResult := .timedOut (some partialResult)
  let decoded : ToolObservation ToolResult ← IO.ofExcept <| fromJson? (toJson observation)
  expect (toJson decoded == toJson observation) "timeout observation lost its partial result in JSON"
  let finished ← complete launched (toJson observation)
  let next := finished.state
  expect (match next.phase with | .controlModel => true | _ => false)
    "timeout continued the dependent suffix"
  expect (next.grant.isNone && next.modelAttempts == launched.state.modelAttempts &&
    next.toolDispatches == 1 && next.responseRepairs == launched.state.responseRepairs &&
    next.retryCount == launched.state.retryCount && next.seenCallIds == launched.state.seenCallIds &&
    toJson next.config == toJson launched.state.config && toJson next.activeView == toJson launched.state.activeView &&
    toJson next.summaries == toJson launched.state.summaries && next.unknownUsage == 0)
    "timeout changed frozen state or refunded/consumed reservations"
  expect (next.artifacts == [artifact] && historyValid next.history)
    "partial artifact retention or closed history is invalid"
  let blocks := resultBlocks next
  expect (blocks.size == 2) "timeout did not settle every admitted call"
  for (block, id) in blocks.toList.zip [processCall.id, suffix.id] do
    expect ((block.getObjValAs? String "tool_use_id").toOption == some id &&
      (block.getObjValAs? Bool "is_error").toOption == some true)
      "timeout result order or error flag is wrong"
  let text ← IO.ofExcept <| blocks[0]!.getObjValAs? String "content"
  let retained : ToolResult ← IO.ofExcept <| (Json.parse text).bind fromJson?
  expect (retained.exitCode.isNone && retained.sha256.isNone && retained.artifacts == #[artifact] &&
    (retained.text.splitOn "partial output").length == 2) "timeout fabricated a target exit/file identity or lost output"
  expect ((blocks[1]!.getObjValAs? String "content").toOption == some timeoutSkippedText)
    "queued call did not receive explicit nonexecution result"
  expect (!finished.pending && finished.suspended.isNone && finished.editWitness.isNone &&
    (checkedTarget finished).isError) "known settlement left a reusable recovery target"
  let records := [intent initial, completion initial (toJson ({} : ControlObservation)),
    intent modeled.state, completion modeled.state (toJson proposal),
    intent queued.state, completion queued.state (toJson ({} : ControlObservation)),
    intent launched.state, completion launched.state (toJson observation)]
  let replayed ← IO.ofExcept <| replay initial records
  expect (toJson replayed.state == toJson next && !replayed.pending && replayed.suspended.isNone)
    "durable timeout did not replay exactly"
  let pending ← IO.ofExcept <| replay initial records.dropLast
  expect (pending.pending && (checkedTarget pending).isOk && (automaticRecovery? pending).isNone)
    "missing timeout completion was incorrectly treated as settled"
  expect ((resolve finished launched.state.nextId (.processAbandoned "already settled")).isError)
    "a completed timeout accepted a second settlement"
  let cancelled ← complete finished (toJson ({cancelled := true} : ControlObservation))
  expect (match (step cancelled.state).1 with | .finish .cancelled => true | _ => false)
    "timeout bypassed cancellation before fresh admission"
  let resumed ← complete finished (toJson ({} : ControlObservation))
  expect (match (step resumed.state).1 with | .model request => historyValid request.messages | _ => false)
    "settled timeout did not permit valid model inspection"
  expect (resumed.state.toolDispatches == 1 && resumed.state.modelAttempts == 2)
    "skipped suffix consumed dispatches or next inference reused its reservation"

  -- Invalid artifact metadata never reverses the already-established settlement.
  let invalidArtifact := {artifact with sha256 := "short"}
  let badPartial := {partialResult with artifacts := #[invalidArtifact]}
  let rejected := consumeTool launched.state call remaining (.timedOut (some badPartial))
  expect (rejected.artifacts.isEmpty && historyValid rejected.history &&
    (match rejected.phase with | .controlModel => true | _ => false))
    "artifact validation manufactured uncertainty or installed an invalid reference"

  -- The same typed observation from the wrong interface is a hard failure,
  -- with no invented result or recovery position.
  let read : ToolCall := {id := "wrong-read", operation := .readFile {path := "main.txt"}}
  for (state, chosen) in [( {launched.state with config := {config with executionProfile := .host}}, call),
      ( {launched.state with phase := .tool read remaining}, read)] do
    let rejected := consumeTool state chosen remaining observation
    expect (match rejected.phase with | .stopped (.failure message) => message == invalidTimeoutText | _ => false)
      "ineligible timeout did not fail closed"
    expect (toJson rejected.history == toJson state.history && rejected.artifacts == state.artifacts)
      "ineligible timeout installed results or artifacts"
    let settled ← complete {state} (toJson observation)
    expect (settled.suspended.isNone && (checkedTarget settled).isError)
      "invalid observation created an unresolved target without uncertainty"
  let ordinary := consumeTool launched.state call remaining (.failure "ordinary command error")
  expect (match ordinary.phase with | .controlTools rest => rest == remaining | _ => false)
    "new timeout semantics changed ordinary tool failure queue behavior"
  IO.println "settled timeout: ordered batch closure, partial output, scope, cancellation and replay passed"

end Tests.SettledTimeout
