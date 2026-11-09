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
    ("action", actionToJson (app := Coding.application) (.wait 10))]
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
  let processCall : ToolCall := {id := "uncertain-process", operation := .runProcess {argv := #["/bin/true"]}}
  let processState := {s1 with phase := .tool processCall [call], toolDispatches := 1}
  let interrupted : ToolObservation ToolResult := .uncertain "lost completion"
  let pending ← IO.ofExcept <| Harness.Recovery.replay processState [intent processState]
  let resolution := Harness.Recovery.Resolution.processCompleted 0 "checked output and settled original process"
  let resolved ← IO.ofExcept <| Harness.Recovery.resolve pending processState.nextId resolution
  check "explicit process resolution preserves the reserved batch and counts" <|
    resolved.state.modelAttempts == processState.modelAttempts && resolved.state.toolDispatches == 1 &&
    resolved.state.nextId == processState.nextId + 1 && !resolved.pending &&
      (match resolved.state.phase with | .controlTools [remaining] => remaining == call | _ => false)
  check "resolution cannot settle an operation twice" <|
    failed (Harness.Recovery.resolve resolved processState.nextId resolution)
  check "resolution must match exact operation ID" <|
    failed (Harness.Recovery.resolve pending (processState.nextId + 1) resolution)
  let uncertain ← IO.ofExcept <| Harness.Recovery.replay processState [intent processState,
    completion processState.nextId (toJson interrupted)]
  check "typed uncertain completion retains the original batch position" <|
    (Harness.Recovery.target uncertain).isSome && !uncertain.pending
  let stopped ← match (step uncertain.state).1 with
    | .finish outcome => IO.ofExcept <| Harness.Recovery.applyRecord uncertain (terminal uncertain.state outcome)
    | _ => throw <| IO.userError "uncertain tool did not stop"
  let resolutionRecord := Json.mkObj [("kind", toJson "resolution"), ("id", toJson processState.nextId),
    ("resolution", toJson resolution), ("source", toJson "operator"), ("resourcesSettled", toJson true)]
  let reopened ← IO.ofExcept <| Harness.Recovery.applyRecord stopped resolutionRecord
  check "durable operator assertion reopens only a recovery stop" <|
    sameState reopened.state resolved.state && !reopened.terminal && reopened.suspended.isNone
  check "operator assertion must attest settled resources" <|
    failed (Harness.Recovery.applyRecord stopped (resolutionRecord.mergeObj
      (Json.mkObj [("resourcesSettled", toJson false)])))
  let pre := String.ofList (List.replicate 64 'a')
  let post := String.ofList (List.replicate 64 'b')
  let editCall : ToolCall := {id := "edit", operation := .editFile {
    path := "file", old := "old", new := "new", expectedSha256 := pre}}
  let editState := {processState with phase := .tool editCall []}
  let witness : Harness.Recovery.EditWitness := {path := "file", preimage := pre, postimage := post}
  let editPending ← IO.ofExcept <| Harness.Recovery.replay editState [
    (intent editState).mergeObj (Json.mkObj [("editWitness", toJson (some witness))])]
  check "preimage cannot be presented as a completed edit" <|
    failed (Harness.Recovery.resolve editPending editState.nextId (.editPostimage pre))
  let reconciled ← IO.ofExcept <| Harness.Recovery.resolve editPending editState.nextId (.editPostimage post)
  check "postimage reconciliation settles without a second reservation" <|
    reconciled.state.toolDispatches == 1 && reconciled.state.nextId == editState.nextId + 1 &&
    (Harness.Recovery.target reconciled).isNone
  IO.println "recovery: journal ordering, typed replay, terminal, and phase serialization checks passed"

end Tests.Recovery
