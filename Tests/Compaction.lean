import Harness.Core.Transition

namespace Tests.Compaction
open Harness Lean

private def expect (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def repeated (n : Nat) : String := String.ofList (List.replicate n 'x')

private def config : Config :=
  {model := "scripted", workspace := "/tmp/compaction", commands := .allow,
   -- Includes the offered schemas: the 75% threshold lies between one and two reads.
   maxContextBytes := 47000, compactAtPercent := 75, compactionKeepMessages := 2,
   maxSummaryBytes := 20000, maxModelAttempts := 12}

private def call (n : Nat) : RawCall :=
  {id := s!"read-{n}", name := "read", input := Json.mkObj [("path", toJson "source.txt")]}

private def callBlock (c : RawCall) : Json :=
  Json.mkObj [("type", toJson "tool_use"), ("id", toJson c.id), ("name", toJson c.name), ("input", c.input)]

private def toolResponse (calls : List RawCall) : ModelObservation :=
  .success {content := (calls.map callBlock).toArray, calls, text := "", stop := .toolUse, usage := some {inputTokens := 10, outputTokens := 2}}

private def textResponse (text : String) : ModelResponse :=
  {content := #[textBlock text], calls := [], text, stop := .endTurn,
   usage := some {inputTokens := 7, outputTokens := 3}}

private def toolResult : ToolObservation ToolResult := .success {text := repeated 6000}

private def seekSummary : Nat → State → List ModelObservation → Except String State
  | 0, _, _ => .error "compaction fixture exhausted fuel"
  | fuel+1, s, responses =>
    match step s with
    | ⟨.control, next⟩ => seekSummary fuel (next {}) responses
    | ⟨.tool _, next⟩ => seekSummary fuel (next toolResult) responses
    | ⟨.model request, next⟩ =>
      if request.purpose == .summary then .ok s
      else match responses with
        | response :: rest => seekSummary fuel (next response) rest
        | [] => .error "expected summary before another task request"
    | ⟨.wait _, next⟩ => seekSummary fuel (next .elapsed) responses
    | _ => .error "fixture stopped before compaction"

private def replySummary (s : State) (observation : ModelObservation) : Except String State :=
  match step s with
  | ⟨.model request, next⟩ =>
    if request.purpose == .summary then .ok (next observation)
    else .error "expected summary-purpose request"
  | _ => .error "expected summary model effect"

private def nextModel : Nat → State → Except String (State × ModelRequest)
  | 0, _ => .error "next model exhausted fuel"
  | fuel+1, s =>
    match step s with
    | ⟨.control, next⟩ => nextModel fuel (next {})
    | ⟨.wait _, next⟩ => nextModel fuel (next .elapsed)
    | ⟨.model request, _⟩ => .ok (s, request)
    | _ => .error "expected next model request"

private def fixture : Except String State :=
  seekSummary 30 (init "compaction" config (repeated 6000))
    [toolResponse [call 1], toolResponse [call 2]]

private def sameRawAndView (before after : State) : Bool :=
  toJson before.history == toJson after.history && toJson before.activeView == toJson after.activeView

def run : IO Unit := do
  let ready ← IO.ofExcept fixture
  let plan ← match ready.pendingSummary with
    | some plan => pure plan
    | none => throw (IO.userError "missing explicit summary plan")
  expect (ready.modelAttempts == 3 && ready.toolDispatches == 2)
    "summary must reserve one attempt after both completed tools"
  expect (plan.sourceStart == 0 && plan.sourceEnd == 3 && ready.history.length == 5)
    "summary source or protocol-valid recent suffix is wrong"
  let request := summaryRequest ready plan
  expect (request.purpose == .summary && request.system == config.instructions &&
    requestBytes request ≤ config.maxContextBytes && historyValid request.messages)
    "summary request must preserve instructions, fit allowance, and close tool calls"
  let installed ← IO.ofExcept (replySummary ready (.success (textResponse "Keep fixing source.txt; two reads completed.")))
  expect (toJson installed.history == toJson ready.history && installed.summaries.length == 1 &&
    installed.activeView.isSome && installed.pendingSummary.isNone)
    "compaction must preserve raw history and retain a durable summary record"
  expect (contextAdmitted installed && historyValid (activeMessages installed) &&
    (activeMessages installed).length == 3 && contextBytes installed < contextBytes ready)
    "installed summary must produce a smaller admitted, paired active context"
  expect (installed.modelAttempts == 3 && installed.knownInputTokens == 27 &&
    installed.knownOutputTokens == 7 && toJson installed.config == toJson ready.config)
    "summary accounting or frozen configuration changed incorrectly"
  let (next, taskRequest) ← IO.ofExcept (nextModel 5 installed)
  expect (next.modelAttempts == 4 && taskRequest.purpose == .task &&
    toJson taskRequest.messages == toJson (activeMessages installed ++ [budgetMessage next]))
    "next task must use the installed view and reserve its own attempt"
  let restored : State ← IO.ofExcept (fromJson? (toJson installed))
  expect (toJson restored == toJson installed && toJson (modelRequest restored) == toJson (modelRequest installed))
    "serialized compaction state must reconstruct the same request"

  let second ← IO.ofExcept (seekSummary 30 installed [toolResponse [call 3], toolResponse [call 4]])
  let secondPlan ← match second.pendingSummary with
    | some plan => pure plan
    | none => throw (IO.userError "missing repeated compaction plan")
  expect (secondPlan.sourceStart == plan.sourceEnd && secondPlan.sourceEnd > plan.sourceEnd &&
    secondPlan.previousSummary.isSome)
    "repeated compaction must cite the previous summary and newly covered raw range"
  let twice ← IO.ofExcept (replySummary second (.success (textResponse "Four reads completed; continue task.")))
  expect (twice.summaries.length == 2 && toJson twice.history == toJson second.history &&
    contextAdmitted twice && historyValid (activeMessages twice))
    "repeated compaction lost history or protocol structure"

  let rejected : List (String × ModelObservation) := [
    ("truncated", .success {textResponse "partial" with stop := .maxTokens}),
    ("refused", .success {textResponse "no" with stop := .refusal}),
    ("context overflow", .success {textResponse "overflow" with stop := .contextOverflow}),
    ("tool use", toolResponse [call 99]),
    ("hidden tool", .success {textResponse "summary" with calls := [call 99]}),
    ("empty", .success (textResponse "")),
    ("summary ceiling", .success (textResponse (repeated 21000))),
    ("installed context ceiling", .success (textResponse (repeated 19000))),
    ("authentication", .failure .authentication "invalid credentials"),
    ("interrupted", .interrupted)]
  for (label, observation) in rejected do
    let failed ← IO.ofExcept (replySummary ready observation)
    expect (sameRawAndView ready failed && failed.summaries.isEmpty &&
      failed.modelAttempts == ready.modelAttempts && failed.toolDispatches == ready.toolDispatches)
      s!"{label}: rejected summary changed context or dispatch accounting"
    match step failed with
    | ⟨.finish _, _⟩ => pure ()
    | _ => throw (IO.userError s!"{label}: rejected summary could dispatch more work")

  let failed ← IO.ofExcept (replySummary ready (.failure .rateLimit "slow down"))
  expect (sameRawAndView ready failed && failed.unknownUsage == ready.unknownUsage + 1)
    "retry must preserve context and account unknown usage"
  let (retry, retryRequest) ← IO.ofExcept (nextModel 5 failed)
  expect (retry.modelAttempts == ready.modelAttempts + 1 && retry.retryCount == 1 &&
    toJson retryRequest == toJson request && toJson retry.pendingSummary == toJson ready.pendingSummary)
    "summary retry must reserve an attempt and retain the exact source request"
  let exhausted := {ready with config := {ready.config with maxModelAttempts := ready.modelAttempts}}
  let stopped ← IO.ofExcept (replySummary exhausted (.uncertain "lost summary response"))
  match step stopped with
  | ⟨.finish _, _⟩ => pure ()
  | _ => throw (IO.userError "summary retry overspent model ceiling")
  let cancelled := consumeControl failed none {cancelled := true}
  expect (sameRawAndView ready cancelled) "cancellation during retry changed the active view"
  match step cancelled with
  | ⟨.finish .cancelled, _⟩ => pure ()
  | _ => throw (IO.userError "cancellation during summary retry was not terminal")

  let batchReady ← IO.ofExcept (seekSummary 30
    (init "batch-boundary" {config with compactAtPercent := 1} (repeated 6000))
    [toolResponse [call 1, call 2]])
  expect (batchReady.toolDispatches == 2 && batchReady.history.length == 3 &&
    historyValid batchReady.history)
    "compaction started before a complete multi-call batch"
  let impossible := admitModel (init "no-space" {config with maxContextBytes := 100} "task")
  match step impossible with
  | ⟨.finish (.limit _), _⟩ => pure ()
  | _ => throw (IO.userError "uncompactable oversized input did not stop clearly")
  IO.println "compaction: successful/repeated summaries, rejection, retries, cancellation, serialization, and batch boundaries passed"

end Tests.Compaction
