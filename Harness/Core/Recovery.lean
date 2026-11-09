import Harness.Core.Transition
import Harness.Core.Turns

/-!
Pure journal replay against `step`: each intent, completion, terminal, recovery and resolution
record must match the core's computed action. Uncertain tool replies suspend their position.
Automatic recovery is limited to lost control, approval, wait, model and read results; edits need a
matching postimage witness and processes need an operator resolution. Checksums and fsync belong to
IO, and replay correspondence proofs are in `Harness.Proofs.Replay`.
-/

namespace Harness.Recovery
open Lean

/-- Recovery never retries a mutation. Lost reads are settled as unknown errors;
only later ordinary core admission may request another read. -/
inductive Disposition where
  | controlLost
  | approvalLost
  | waitLost
  | modelLost
  | readLost
  | mutationAbandoned (note : String)
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

inductive Provenance where
  | automatic
  | operator
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

def Disposition.provenance : Disposition → Provenance
  | .mutationAbandoned _ => .operator
  | _ => .automatic

structure RecoveryRecord where
  version : Nat := 1
  disposition : Disposition
  provenance : Provenance
  deriving Repr, ToJson, FromJson

/-- The same typed record constructor is used by the runner and replay tests. -/
def recoveryRecord (id : Nat) (disposition : Disposition) : Json :=
  Json.mkObj [("kind", toJson "recovery"), ("id", toJson id),
    ("recovery", toJson ({ disposition, provenance := disposition.provenance } : RecoveryRecord))]

structure Cursor (app : Application := Coding.application) where
  state : State app
  pending : Bool := false
  terminal : Bool := false
  editWitness : Option app.Witness := none
  suspended : Option (State app) := none

variable {app : Application}

/-- An uncertain observation does not settle the original tool-call position. -/
def target (cursor : Cursor app) : Option (State app) :=
  if cursor.pending then some cursor.state else cursor.suspended

/-- A hard terminal cannot be reopened, even if supplied with a forged suspended
field. Valid replay additionally relates the saved tool position to this stop. -/
def checkedTarget (cursor : Cursor app) : Except String (State app) := do
  if cursor.pending then
    if cursor.terminal || cursor.suspended.isSome then throw "invalid pending recovery cursor"
    pure cursor.state
  else
    let some prior := cursor.suspended | throw "no unresolved operation to recover"
    match cursor.state.phase with
    | .stopped (.recoveryRequired _) =>
      match (step prior).1 with
      | .tool _ => pure {prior with artifacts := cursor.state.artifacts}
      | _ => throw "suspended recovery position is not a tool"
    | _ => throw "only an uncertain tool stop can be reopened"

def validateWitness (action : Action app) (witness : app.Witness) : Except String Unit := do
  match action with
  | .tool call => app.validateWitness call.operation witness
  | _ => throw "application witness attached to a non-tool operation"

private def validNote (note : String) : Bool :=
  !note.trimAscii.toString.isEmpty && note.utf8ByteSize ≤ 2048

/-- Resolve only an existing uncertain tool position. Counts and pending batch
are inherited from its reserved state; this function emits no external effect. -/
def resolve (cursor : Cursor app) (id : Nat) (resolution : app.Resolution) : Except String (Cursor app) := do
  let prior ← checkedTarget cursor
  unless id == prior.nextId do throw "resolution operation ID does not match unresolved operation"
  let node := step prior
  match node with
  | ⟨.tool call, continuation⟩ =>
    let settled ← app.resolve call.operation cursor.editWitness resolution
    return {state := continuation settled.observation}
  | _ => throw "only an unresolved tool operation can be resolved"

/-- Consume an explicit recovery disposition. Restarting an observation advances
its operation ID without claiming to have received its missing answer. This is an
administrative transition, not a second execution loop. -/
def recover (cursor : Cursor app) (id : Nat) (disposition : Disposition) : Except String (Cursor app) := do
  let prior ← checkedTarget cursor
  unless id == prior.nextId do throw "recovery operation ID does not match unresolved operation"
  let node := step prior
  let next ← match node, disposition with
    | ⟨.control, _⟩, .controlLost =>
      pure (advance {prior with grant := none})
    | ⟨.ask _, _⟩, .approvalLost =>
      match prior.phase with
      | .ask call remaining =>
        pure (advance {prior with phase := .controlTools (call :: remaining), grant := none})
      | _ => throw "approval recovery requires its admitted queue"
    | ⟨.wait _, _⟩, .waitLost =>
      pure (advance {prior with grant := none})
    | ⟨.model _, continuation⟩, .modelLost =>
      pure (continuation (ModelObservation.uncertain
        "model response lost during interruption; prior usage is unknown"))
    | ⟨.tool call, continuation⟩, .readLost =>
      if app.readOnly call.operation then
        pure (continuation (ToolObservation.failure
          "Read result lost during interruption; original outcome is unknown. No read was repeated. Request a new read if needed."))
      else throw "automatic lost-read recovery cannot settle a mutation"
    | ⟨.tool call, continuation⟩, .mutationAbandoned note => do
      unless validNote note do throw "abandonment requires a nonempty note of at most 2048 bytes"
      if app.mayAbandon call.operation then
        pure (continuation (ToolObservation.failure
          s!"Operator abandoned uncertain file mutation; prior effects remain unknown and no mutation was repeated: {note}"))
      else throw "this application operation cannot be abandoned"
    | _, _ => throw "recovery disposition does not match unresolved operation"
  return {state := next}

/-- Choose only safe automatic dispositions. Mutations require their existing
witnessed reconciliation or an explicit operator decision. -/
def automaticRecovery? (cursor : Cursor app) : Option Disposition := do
  let prior ← (checkedTarget cursor).toOption
  match (step prior).1 with
  | .control => some .controlLost
  | .ask _ => some .approvalLost
  | .wait _ => some .waitLost
  | .model _ => some .modelLost
  | .tool call => if app.readOnly call.operation then some .readLost else none
  | .finish _ => none

/-- Uncertainty is classified from the same decoded reply passed to `step`. -/
def replyIsUncertain : (action : Action app) → Reply action → Bool
  | .tool _, .interrupted _ _ | .tool _, .uncertain _ _ => true
  | .tool _, _ | .control, _ | .model _, _ | .ask _, _ | .wait _, _ => false
  | .finish _, response => nomatch response

/-- A completed journal operation follows the actual coalgebra continuation.
Only an uncertain tool reply retains its exact pre-operation position. -/
def complete (cursor : Cursor app) (response : Reply (step cursor.state).1) : Cursor app :=
  let uncertain := replyIsUncertain (step cursor.state).1 response
  {state := (step cursor.state).2 response,
   suspended := if uncertain then some cursor.state else none,
   editWitness := if uncertain then cursor.editWitness else none}

/-- Reopen only a durably ended, settled turn. The record consumes its own
operation identity; duplicate records cannot append the same user task twice. -/
def newTurn (cursor : Cursor app) (id turn : Nat) (task : String) : Except String (Cursor app) := do
  unless cursor.terminal do throw "follow-up requires a durable terminal record"
  if cursor.pending || cursor.suspended.isSome || cursor.editWitness.isSome then
    throw "follow-up blocked by unresolved operation or recovery evidence"
  unless id == cursor.state.nextId && turn == cursor.state.turn + 1 do
    throw "follow-up operation or turn identity does not match session"
  return {state := ← beginTurn cursor.state task}

def userTurnRecord (id turn : Nat) (task : String) : Json :=
  Json.mkObj [("kind", toJson "user_turn"), ("id", toJson id),
    ("turn", toJson turn), ("task", toJson task)]

/-- Records are ordered by the framed journal; an intent must match the next executable action. -/
def applyRecord (cursor : Cursor app) (record : Json) : Except String (Cursor app) := do
  let kind ← record.getObjValAs? String "kind"
  let id ← record.getObjValAs? Nat "id"
  if kind == "recovery" then
    let saved ← record.getObjValAs? RecoveryRecord "recovery"
    unless saved.version == 1 && saved.provenance == saved.disposition.provenance do
      throw "unsupported recovery record version or invalid provenance"
    return ← recover cursor id saved.disposition
  if kind == "resolution" then
    let resolution ← record.getObjValAs? app.Resolution "resolution"
    let source ← record.getObjValAs? String "source"
    if app.operatorResolution resolution then
      unless source == "operator" && (record.getObjValAs? Bool "resourcesSettled").toOption == some true do
        throw "resolution requires operator provenance and settled-resource assertion"
    else
      unless source == "application_evidence" do throw "invalid application resolution provenance"
    return ← resolve cursor id resolution
  if kind == "user_turn" then
    return ← newTurn cursor id (← record.getObjValAs? Nat "turn") (← record.getObjValAs? String "task")
  if cursor.terminal then throw "record after terminal outcome"
  if id != cursor.state.nextId then throw "operation ID does not match replay state"
  let node := step cursor.state
  match kind with
  | "intent" =>
    if cursor.pending then throw "second intent without completion"
    let action ← record.getObjVal? "action"
    if action.compress != (actionToJson node.1).compress then
      throw "intent differs from pure core action"
    match node.1 with
    | .finish _ => throw "terminal action cannot have an external intent"
    | _ =>
      let witness ← match record.getObjVal? "editWitness" with
        | .error _ => pure none
        | .ok value => fromJson? value
      if let some witness := witness then validateWitness node.1 witness
      return { cursor with pending := true, editWitness := witness }
  | "completion" =>
    if !cursor.pending then throw "completion without intent"
    let observation ← record.getObjVal? "observation"
    let reply ← replyFromJson node.1 observation
    return complete cursor reply
  | "terminal" =>
    if cursor.pending then throw "terminal record with unresolved intent"
    match node.1 with
    | .finish outcome =>
      let saved ← record.getObjVal? "outcome"
      if saved.compress != (toJson outcome).compress then throw "terminal outcome mismatch"
      return { cursor with terminal := true }
    | _ => throw "premature terminal record"
  | _ => throw "unknown journal record"

def replay (initial : State app) (records : List Json) : Except String (Cursor app) :=
  records.foldlM applyRecord { state := initial }

/-- Replay is deterministic for the same initial state and valid record sequence. -/
theorem replay_deterministic (s : State app) (records : List Json) (a b : Cursor app)
    (ha : replay s records = .ok a) (hb : replay s records = .ok b) : a = b := by
  have h : (Except.ok a : Except String (Cursor app)) = .ok b := ha.symm.trans hb
  exact Except.ok.inj h

end Harness.Recovery
