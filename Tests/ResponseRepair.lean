import Tests.Core
import Harness.Core.Recovery

/-! Response repair through emitted actions, durable replay and cancellation.
The scripted tools record actual dispatches; rejected proposals cannot count as work. -/
namespace Tests.ResponseRepair
open Lean Harness Harness.Recovery Tests.Core

private def config : Config :=
  {cfg with maxModelAttempts := 8, maxResponseRepairs := 2, compactionEnabled := false}

private def response (calls : List RawCall) : ModelObservation := .success {
  content := calls.toArray.map callBlock, calls, text := "", stop := .toolUse,
  usage := some {inputTokens := 11, outputTokens := 7} }

private def badBatch : ModelObservation := response [processCall,
  raw "short-hash" "edit" (toJson ({
    path := "main.txt", old := "broken", new := "fixed", expectedSha256 := "short"} : EditArgs))]

private def same (a b : State) : Bool := toJson a == toJson b

/-- Save actual intents and observations, then exercise the ordinary replay reader. -/
private def complete (cursor : Cursor) (records : List Json) (observation : Json) :
    IO (Cursor × List Json) := do
  let intent := Json.mkObj [("kind", toJson "intent"), ("id", toJson cursor.state.nextId),
    ("action", actionToJson (step cursor.state).1)]
  let completion := Json.mkObj [("kind", toJson "completion"), ("id", toJson cursor.state.nextId),
    ("observation", observation)]
  let waiting ← IO.ofExcept <| applyRecord cursor intent
  let next ← IO.ofExcept <| applyRecord waiting completion
  return (next, records ++ [intent, completion])

def run : IO Unit := do
  let initial := init "response-repair" config "repair and test the file"
  let observed ← IO.ofExcept <| observeScript 60 initial
    [badBatch, toolResponse readCall, finalResponse] [] []
  expect (observed.effects.map (·.id) == [readCall.id])
    "valid first call in rejected batch dispatched"
  expect (observed.state.responseRepairs == 1 && observed.state.modelAttempts == 3 &&
    observed.state.toolDispatches == 1) "repair did not reserve a fresh inference"
  expect (match observed.state.phase with | .stopped (.final _) => true | _ => false)
    "corrected response could not finish"
  let some repairRequest := observed.requests[1]? | throw <| IO.userError "no repair request"
  expect (toJson repairRequest.messages == toJson
    (initial.history ++ [responseRepairMessage .invalidBatch,
      budgetMessage {initial with modelAttempts := 2}]))
    "rejected assistant content or calls entered the next request"
  expect (observed.state.seenCallIds == [readCall.id]) "rejected IDs were admitted"

  let model := admitModel initial
  let repaired := consumeModel model badBatch
  expect (repaired.modelAttempts == 1 && repaired.toolDispatches == 0 &&
    repaired.knownInputTokens == 11 && repaired.knownOutputTokens == 7 &&
    repaired.unknownUsage == 0 && repaired.grant.isNone) "repair lost usage or gained authority"
  expect (match (step repaired).1 with | .control => true | _ => false)
    "repair bypassed cancellation observation"
  let cancelled := consumeControl repaired none {cancelled := true}
  expect (match (step cancelled).1 with | .finish .cancelled => true | _ => false)
    "cancellation admitted a repair attempt"
  expect (cancelled.modelAttempts == 1 && cancelled.toolDispatches == 0)
    "cancellation consumed a new dispatch reservation"
  let expired := consumeControl repaired none {deadlineExceeded := true}
  expect (match (step expired).1 with | .finish (.limit _) => true | _ => false)
    "deadline admitted a repair attempt"

  let truncated := consumeModel model (.success {
    content := #[callBlock processCall], calls := [processCall], text := "", stop := .maxTokens,
    usage := some {inputTokens := 5, outputTokens := 4096}})
  expect (truncated.responseRepairs == 1 && truncated.toolDispatches == 0 &&
    truncated.seenCallIds.isEmpty && truncated.knownOutputTokens == 4096 &&
    toJson truncated.history == toJson (initial.history ++ [responseRepairMessage .truncated]))
    "truncated output entered history, authorized work or lost usage"
  let malformed := consumeModel {model with retryCount := 1} (.failure .malformed "private diagnostic")
  expect (malformed.responseRepairs == 1 && malformed.retryCount == 1 &&
    malformed.unknownUsage == 1 && malformed.knownInputTokens == 0 &&
    toJson malformed.history == toJson (initial.history ++ [responseRepairMessage .malformed]))
    "malformed repair refunded retries, fabricated usage or reflected diagnostic text"
  let rateLimited := consumeModel {model with responseRepairs := 1} (.failure .rateLimit "429")
  expect (rateLimited.responseRepairs == 1 && rateLimited.retryCount == 1)
    "transport retry consumed or refunded response-repair allowance"
  for kind in [ResponseRepairKind.invalidBatch, .truncated, .malformed] do
    expect ((responseRepairText kind).utf8ByteSize <= 1024) "repair feedback exceeded byte cap"

  let once := init "replay-repair" {config with maxResponseRepairs := 1} "task"
  let (started, first) ← complete {state := once} [] (toJson ({} : ControlObservation))
  let (saved, records) ← complete started first (toJson (ModelObservation.failure .malformed "bad"))
  let replayed ← IO.ofExcept <| replay once records
  expect (same replayed.state saved.state && replayed.state.responseRepairs == 1)
    "replay refunded response-repair allowance"
  let restored : State ← IO.ofExcept <| fromJson? (toJson replayed.state)
  expect (same restored replayed.state) "response-repair state did not survive serialization"
  let waiting ← IO.ofExcept <| applyRecord {replayed with state := restored} <| Json.mkObj [
    ("kind", toJson "intent"), ("id", toJson restored.nextId),
    ("action", actionToJson (step restored).1)]
  let recovered ← IO.ofExcept <| applyRecord waiting (recoveryRecord restored.nextId .controlLost)
  expect (recovered.state.responseRepairs == 1) "lost control recovery reset repair count"
  let (again, _) ← complete recovered [] (toJson ({} : ControlObservation))
  let (exhausted, _) ← complete again [] (toJson (ModelObservation.failure .malformed "bad again"))
  expect (isFailure exhausted.state && exhausted.state.responseRepairs == 1 &&
    exhausted.state.modelAttempts == 2 && exhausted.state.unknownUsage == 2 &&
    toJson exhausted.state.history == toJson saved.state.history)
    "restarted session exceeded repair ceiling or fabricated another feedback turn"
  let noAttempts := admitModel (init "one-attempt" {config with maxModelAttempts := 1} "task")
  expect (isFailure (consumeModel noAttempts badBatch) &&
    (consumeModel noAttempts badBatch).responseRepairs == 0) "repair ignored model ceiling"
  let disabled := admitModel (init "disabled" {config with maxResponseRepairs := 0} "task")
  expect (isFailure (consumeModel disabled badBatch) &&
    toJson (consumeModel disabled badBatch).history == toJson disabled.history)
    "disabled repair changed history"

  let summary := consumeSummary model {sourceStart := 0, sourceEnd := 1, previousSummary := none}
    (.failure .malformed "bad summary")
  expect (isFailure summary && summary.responseRepairs == 0 &&
    toJson summary.history == toJson initial.history) "summary failure entered task repair"
  IO.println "response repair: whole-batch rejection, fresh admission, ceilings, cancellation and replay passed"

end Tests.ResponseRepair
