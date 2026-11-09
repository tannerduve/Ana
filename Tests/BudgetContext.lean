import Harness.Core.Recovery

/-! Request-only budget notices follow reservations, including retry and summary
costs. Boundary checks exercise the exact request eventually emitted by `step`. -/
namespace Tests.BudgetContext
open Harness Lean

private def expect (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def config : Config :=
  {model := "scripted", workspace := "/tmp/budget-context", maxModelAttempts := 10,
    maxToolCalls := 3, maxOutputTokens := 77, compactionEnabled := false}

private def expectNotice (state : State) (models tools : Nat) : IO Unit := do
  let request := modelRequest state
  let message ← match request.messages.getLast? with
    | some message => pure message
    | none => throw <| IO.userError "missing request messages"
  let text ← IO.ofExcept <| message.content[0]!.getObjValAs? String "text"
  expect (text.startsWith s!"[Harness limits] After this request, at most {models} further model requests and {tools} tool executions remain.")
    "notice does not match independent expected remaining counters"
  expect ((text.splitOn s!"Configured operation time limit: {state.config.operationTimeoutMs} ms; cleanup may take additional time.").length == 2 &&
    (text.splitOn "The remaining invocation deadline may shorten this limit.").length == 2 &&
    (text.splitOn "An interrupted operation may have partial effects; inspect them before continuing.").length == 2)
    "duration notice omitted the configured bound, cleanup or invocation caveat"
  expect (historyValid request.messages) "budget notice broke tool pairing"

private def expectModel (state : State) : IO ModelRequest := do
  match step state with
  | ⟨.model request, _⟩ => pure request
  | _ => throw <| IO.userError "expected admitted model action"

def run : IO Unit := do
  let initial := init "budget-context" config "repair the parser"
  let first := consumeControl initial none {}
  let _ ← expectModel first
  expect (first.modelAttempts == 1 && toJson first.history == toJson initial.history)
    "initial reservation changed history or counted twice"
  expectNotice first 9 3
  for milliseconds in [0, 1500, 90000] do
    let different := admitTask (init "duration" {config with operationTimeoutMs := milliseconds} "task")
    expectNotice different 9 3
    expect (different.history.length == 1 && different.activeView.isNone)
      "duration notice changed authoritative history or installed a context view"

  let penultimate := admitTask {initial with modelAttempts := 8}
  let last := admitTask {initial with modelAttempts := 9}
  let _ ← expectModel penultimate
  let _ ← expectModel last
  expectNotice penultimate 1 3
  expectNotice last 0 3
  match step (admitTask last) with
  | ⟨.finish (.limit _), _⟩ => pure ()
  | _ => throw <| IO.userError "notice allowed an extra request"

  let retrying := consumeModel first (.failure .rateLimit "retry later")
  let retry := consumeControl (consumeWait retrying .elapsed) none {}
  expectNotice retry 8 3
  let repaired := consumeControl (consumeModel retry (.failure .malformed "bad stream")) none {}
  expectNotice repaired 7 3
  expect (repaired.modelAttempts == 3 && repaired.responseRepairs == 1)
    "retry or response repair failed to consume a fresh reservation"
  expect (repaired.history.length == 2)
    "request-only notices accumulated in authoritative history"

  let raw : RawCall := {id := "read-1", name := "read", input := Json.mkObj [("path", toJson "source")]}
  let block := Json.mkObj [("type", toJson "tool_use"), ("id", toJson raw.id),
    ("name", toJson raw.name), ("input", raw.input)]
  let proposed := consumeModel first (.success {
    content := #[block], calls := [raw], text := "",
    stop := .toolUse, usage := some {inputTokens := 10, outputTokens := 2}})
  let call ← match proposed.phase with
    | .controlTools [call] => pure call
    | _ => throw <| IO.userError "read fixture was not admitted"
  let tool := consumeControl proposed (some [call]) {}
  let done := consumeTool tool call [] (.success {text := "file contents"})
  let next := consumeControl (consumeControl done (some []) {}) none {}
  expectNotice next 8 2
  expect (next.history.length == 3 && historyValid next.history)
    "tool result pairing or authoritative history changed"
  let restored : State ← IO.ofExcept (fromJson? (toJson next))
  expect (toJson (modelRequest restored) == toJson (modelRequest next))
    "restored ledger did not reconstruct the exact request"

  -- Replay a durable retry prefix, then validate its pending request. A stale
  -- notice from before the second reservation must fail exact intent matching.
  let intent (state : State) := Json.mkObj [("kind", toJson "intent"),
    ("id", toJson state.nextId), ("action", actionToJson (step state).1)]
  let completion (id : Nat) (observation : Json) := Json.mkObj
    [("kind", toJson "completion"), ("id", toJson id), ("observation", observation)]
  let control : ControlObservation := {}
  let failure : ModelObservation := .failure .rateLimit "retry later"
  let s1 := advance (consumeControl initial none control)
  let s2 := advance (consumeModel s1 failure)
  let s3 := advance (consumeWait s2 .elapsed)
  let s4 := advance (consumeControl s3 none control)
  let records := [intent initial, completion 0 (toJson control),
    intent s1, completion 1 (toJson failure), intent s2, completion 2 (toJson WaitObservation.elapsed),
    intent s3, completion 3 (toJson control)]
  let replayed ← IO.ofExcept <| Harness.Recovery.replay initial (records ++ [intent s4])
  expect (replayed.pending && toJson replayed.state == toJson s4 &&
    toJson (modelRequest replayed.state) == toJson (modelRequest s4))
    "journal replay reconstructed a different reserved request"
  expectNotice replayed.state 8 3
  let staleIntent := Json.mkObj [("kind", toJson "intent"), ("id", toJson s4.nextId),
    ("action", actionToJson (app := Coding.application) (.model (modelRequest s1)))]
  match Harness.Recovery.replay initial (records ++ [staleIntent]) with
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError "replay accepted a stale budget notice"

  -- A summary shares the model ledger but does not retain an obsolete notice.
  let summaryState := {done with history := done.history ++
    [{role := "assistant", content := #[textBlock "still investigating"]},
     {role := "user", content := #[textBlock "continue"]}]}
  let plan : SummaryPlan := {sourceStart := 0, sourceEnd := 3, previousSummary := none}
  let summary := admitSummary summaryState plan
  expect (summary.modelAttempts == 2) "summary did not reserve from the shared budget"
  expect (toJson (summaryRequest summary plan).messages ==
    toJson (summarySource summary plan ++ [{role := "user", content := #[textBlock summaryInstruction]}]))
    "summary source acquired request-only budget metadata"
  let text := "Read source; parser still needs repair."
  let installed := consumeSummary summary plan (.success {
    content := #[textBlock text], calls := [],
    text, stop := .endTurn, usage := some {inputTokens := 5, outputTokens := 3}})
  expect (installed.summaries.length == 1) "summary fixture did not install"
  expectNotice (consumeControl installed none {}) 7 2

  -- Reservation changes the decimal width: 10 remaining becomes 9. Admission
  -- must examine that emitted request, including the notice, at the exact cap.
  let reserved := {initial with modelAttempts := 1, phase := .model}
  let exactBytes := requestBytes (modelRequest reserved)
  expect (requestBytes (modelRequest initial) > exactBytes) "decimal boundary fixture did not differ"
  let exact := {initial with config := {config with maxContextBytes := exactBytes}}
  let accepted := admitTask exact
  let emitted ← expectModel accepted
  expect (requestBytes emitted == exactBytes && accepted.modelAttempts == 1)
    "checked request and emitted request differ at the context ceiling"
  let denied := admitTask {exact with config := {exact.config with maxContextBytes := exactBytes - 1}}
  expect (denied.modelAttempts == 0) "failed admission consumed a phantom reservation"
  match step denied with
  | ⟨.finish (.limit _), _⟩ => pure ()
  | _ => throw <| IO.userError "oversized request was admitted"
  let cancelled := consumeControl initial none {cancelled := true}
  expect (cancelled.modelAttempts == 0) "cancellation consumed a reservation"
  match step cancelled with
  | ⟨.finish .cancelled, _⟩ => pure ()
  | _ => throw <| IO.userError "notice bypassed cancellation"
  IO.println "budget context: reservations, retries, repair, tools, summaries, restore, byte admission and cancellation passed"

end Tests.BudgetContext
