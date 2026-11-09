import Harness.Core.Recovery

namespace Tests.Recovery
open Lean Harness

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError s!"recovery test failed: {label}"

private def cfg : Config := { model := "fixture-model", workspace := "/fixture", commands := .allow }
private def initial : State := init "fixture-session" cfg "Inspect and repair the fixture"

private def intent (s : State) : Json :=
  Json.mkObj [("kind", toJson "intent"), ("id", toJson s.nextId),
    ("action", actionToJson (step s).1)]

private def completion (id : Nat) (observation : Json) : Json :=
  Json.mkObj [("kind", toJson "completion"), ("id", toJson id), ("observation", observation)]

private def terminal (s : State) (outcome : Outcome) : Json :=
  Json.mkObj [("kind", toJson "terminal"), ("id", toJson s.nextId), ("outcome", toJson outcome)]

private def failed {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def sameState (a b : State) : Bool := (toJson a).compress == (toJson b).compress

/-- Completed records replay by typed continuations, with no external interpreter. -/
def run : IO Unit := do
  let control : ControlObservation := {}
  let s1 := advance (consumeControl initial none control)
  let first := [intent initial, completion 0 (toJson control)]
  check "empty replay preserves initial state" <|
    match Harness.Recovery.replay initial [] with
    | .ok c => sameState c.state initial && !c.pending && !c.terminal
    | .error _ => false
  check "uncompleted intent remains explicit" <|
    match Harness.Recovery.replay initial [intent initial] with
    | .ok c => c.pending && sameState c.state initial
    | .error _ => false
  check "completed control matches live continuation" <|
    match Harness.Recovery.replay initial first with
    | .ok c => sameState c.state s1 && !c.pending && c.state.modelAttempts == 1
    | .error _ => false
  check "unknown record kind refused" <|
    failed (Harness.Recovery.replay initial [Json.mkObj [("kind", toJson "future"), ("id", toJson (0 : Nat))]])
  check "completion without intent refused" <|
    failed (Harness.Recovery.replay initial [completion 0 (toJson control)])
  check "duplicate intent refused" <|
    failed (Harness.Recovery.replay initial [intent initial, intent initial])
  check "out-of-order identity refused" <|
    failed (Harness.Recovery.replay initial [intent initial, completion 9 (toJson control)])
  check "duplicate completion refused" <|
    failed (Harness.Recovery.replay initial (first ++ [completion 0 (toJson control)]))
  let wrongIntent := Json.mkObj [("kind", toJson "intent"), ("id", toJson (0 : Nat)),
    ("action", actionToJson (.wait 10))]
  check "mismatching executable action refused" <|
    failed (Harness.Recovery.replay initial [wrongIntent])
  check "wrong observation type refused" <|
    failed (Harness.Recovery.replay initial [intent initial, completion 0 (toJson "approved")])
  let outcome := Outcome.final "finished"
  let response : ModelResponse := { content := #[textBlock "finished"], calls := [], text := "finished", stop := .endTurn }
  let observation := ModelObservation.success response
  let s2 := advance (consumeModel s1 observation)
  let completed := first ++ [intent s1, completion 1 (toJson observation)]
  check "completed inference replay matches execution" <|
    match Harness.Recovery.replay initial completed with
    | .ok c => sameState c.state s2 && c.state.modelAttempts == 1 && c.state.unknownUsage == 1
    | .error _ => false
  let finished := completed ++ [terminal s2 outcome]
  check "terminal outcome recorded" <|
    match Harness.Recovery.replay initial finished with
    | .ok c => c.terminal && !c.pending && sameState c.state s2
    | .error _ => false
  check "premature terminal refused" <|
    failed (Harness.Recovery.replay initial [terminal initial outcome])
  check "terminal with unresolved intent refused" <|
    failed (Harness.Recovery.replay initial [intent initial, terminal initial outcome])
  check "mismatching final answer refused" <|
    failed (Harness.Recovery.replay initial (completed ++ [terminal s2 (.final "different")]))
  check "post-terminal records refused" <|
    failed (Harness.Recovery.replay initial (finished ++ [terminal s2 outcome]))
  check "external intent for finished state refused" <|
    failed (Harness.Recovery.replay initial (completed ++ [intent s2]))
  let call : ToolCall := { id := "read-1", operation := .readFile {path := "README.md"} }
  let phases : List Phase := [.controlModel, .model, .controlTools [call], .ask call [],
    .tool call [], .waiting 1000, .stopped outcome]
  for phase in phases do
    let state := {s1 with phase := phase, grant := some call}
    let decoded : Except String State := fromJson? (toJson state)
    check "phase/state JSON roundtrip" <| match decoded with
      | .ok restored => sameState state restored
      | .error _ => false
  -- A replayed tool completion appends one authoritative result and consumes
  -- the grant; replay never needs filesystem/process access to reconstruct it.
  let toolState := {s1 with phase := .tool call [], toolDispatches := 1, grant := some call}
  let toolReply : ToolObservation ToolResult := .success {text := "fixture text"}
  let toolNext := advance (consumeTool toolState call [] toolReply)
  check "tool completion reconstructs exactly once" <|
    match Harness.Recovery.replay toolState [intent toolState, completion toolState.nextId (toJson toolReply)] with
    | .ok c => sameState c.state toolNext && c.state.grant.isNone
    | .error _ => false
  check "tool completion cannot be applied twice" <|
    failed (Harness.Recovery.replay toolState [intent toolState,
      completion toolState.nextId (toJson toolReply), completion toolState.nextId (toJson toolReply)])
  -- A valid journal frame can still contain an internally inconsistent typed
  -- model success. Replay must enforce the core's response contract without
  -- relying on the provider adapter having produced that observation.
  let raw : RawCall := {id := call.id, name := "read", input := Json.mkObj [("path", toJson "README.md")]}
  let inconsistent : ModelObservation := .success {
    content := #[], calls := [raw], text := "", stop := .toolUse,
    usage := some {inputTokens := 19, outputTokens := 3} }
  let decoded : ModelObservation ← IO.ofExcept <| fromJson? (toJson inconsistent)
  check "inconsistent observation retains the existing JSON representation" <|
    (toJson decoded).compress == (toJson inconsistent).compress
  let recorded := first ++ [intent s1, completion s1.nextId (toJson decoded)]
  let rejected ← IO.ofExcept <| Harness.Recovery.replay initial recorded
  check "completed inconsistent model observation replays to failure" <|
    match (step rejected.state).fst with | .finish (.failure _) => true | _ => false
  check "rejection leaves no admitted calls or altered history" <|
    rejected.state.toolDispatches == 0 && rejected.state.seenCallIds.isEmpty &&
      (toJson rejected.state.history).compress == (toJson initial.history).compress
  check "rejection preserves reservation and reported usage" <|
    rejected.state.modelAttempts == 1 && rejected.state.knownInputTokens == 19 &&
      rejected.state.knownOutputTokens == 3 && rejected.state.unknownUsage == 0 &&
      rejected.state.nextId == 2 && !rejected.pending && !rejected.terminal
  let illicitToolIntent := Json.mkObj [("kind", toJson "intent"),
    ("id", toJson rejected.state.nextId), ("action", actionToJson (.tool call))]
  check "corrupt-success replay cannot continue with tool dispatch" <|
    failed (Harness.Recovery.replay initial (recorded ++ [illicitToolIntent]))
  match (step rejected.state).fst with
  | .finish failure =>
    check "replayed consistency failure can be durably terminated" <|
      match Harness.Recovery.replay initial (recorded ++ [terminal rejected.state failure]) with
      | .ok c => c.terminal && !c.pending && c.state.toolDispatches == 0
      | .error _ => false
  | _ => throw <| IO.userError "consistency failure emitted a nonterminal action"
  IO.println "recovery: journal ordering, typed replay, terminal, and phase serialization checks passed"

end Tests.Recovery
