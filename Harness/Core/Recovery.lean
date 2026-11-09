import Harness.Core.Transition

/-!
# Journal Replay and Recovery

Purely replays journal records against `step`. `applyRecord` checks each intent, completion and
terminal record against the action computed by the core. `replay` folds the records into a
`Cursor`. Interrupted or uncertain tool observations leave a suspended position. `resolve`
settles that position with a `Resolution`: an edit postimage checked by `EditWitness`, or an
operator assertion about a process.

Storage checksums and fsync are IO concerns handled elsewhere. `replay_deterministic` proves
determinism only. Administrative recovery traces are not currently connected to `Reachable`
proofs.
-/

namespace Harness.Recovery
open Lean

structure EditWitness where
  version : Nat := 1
  path : String
  preimage : String
  postimage : String
  deriving Repr, ToJson, FromJson

/-- These record observations or operator assertions, never exactly-once claims. -/
inductive Resolution where
  | editPostimage (observed : String)
  | processCompleted (exitCode : Int) (note : String)
  | processAbandoned (note : String)
  deriving Repr, ToJson, FromJson

structure Cursor where
  state : State
  pending : Bool := false
  terminal : Bool := false
  editWitness : Option EditWitness := none
  suspended : Option State := none

/-- An uncertain observation does not settle the original tool-call position. -/
def target (cursor : Cursor) : Option State :=
  if cursor.pending then some cursor.state else cursor.suspended

private def validHash (hash : String) : Bool :=
  hash.length == 64 && hash.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

private def validateWitness (action : Action) (witness : EditWitness) : Except String Unit := do
  match action with
  | .tool {operation := .editFile args, ..} =>
    unless witness.version == 1 && witness.path == args.path &&
        witness.preimage == args.expectedSha256 && validHash witness.preimage && validHash witness.postimage do
      throw "edit witness does not match admitted operation"
  | _ => throw "edit witness attached to a different operation"

private def validNote (note : String) : Bool :=
  !note.trimAscii.toString.isEmpty && note.utf8ByteSize ≤ 2048

/-- Resolve only an existing uncertain tool position. Counts and pending batch
are inherited from its reserved state; this function emits no external effect. -/
def resolve (cursor : Cursor) (id : Nat) (resolution : Resolution) : Except String Cursor := do
  let some prior := target cursor | throw "no unresolved operation to resolve"
  unless id == prior.nextId do throw "resolution operation ID does not match unresolved operation"
  let node := step prior
  match action : node.1 with
  | .tool call =>
    let reply : ToolObservation ToolResult ← match call.operation, resolution with
      | .editFile _, .editPostimage observed => do
        let some witness := cursor.editWitness | throw "edit intent has no preimage/postimage witness"
        validateWitness (.tool call) witness
        unless observed == witness.postimage do throw "observed file identity does not match intended postimage"
        pure <| .success {text := s!"reconciled {witness.path}: current contents match intended postimage; execution count is unknown", sha256 := some observed}
      | .runProcess _, .processCompleted code note => do
        unless validNote note && 0 ≤ code && code ≤ 255 do throw "completion requires an exit code in 0..255 and a nonempty note of at most 2048 bytes"
        pure <| .success {text := s!"Operator-reported completion; not independently verified: {note}", exitCode := some code}
      | .runProcess _, .processAbandoned note => do
        unless validNote note do throw "abandonment requires a nonempty note of at most 2048 bytes"
        pure <| .failure s!"Operator abandoned uncertain command; prior effects remain unknown and the command was not repeated: {note}"
      | _, _ => throw "resolution does not apply to the unresolved operation"
    return {state := node.2 (action ▸ reply)}
  | _ => throw "only unresolved edits and processes can be resolved"

/-- Records are ordered by the framed journal; an intent must match the next executable action. -/
def applyRecord (cursor : Cursor) (record : Json) : Except String Cursor := do
  let kind ← record.getObjValAs? String "kind"
  let id ← record.getObjValAs? Nat "id"
  if kind == "resolution" then
    let resolution ← record.getObjValAs? Resolution "resolution"
    let source ← record.getObjValAs? String "source"
    match resolution with
    | .editPostimage _ => unless source == "file_identity" do throw "invalid edit resolution provenance"
    | _ =>
      unless source == "operator" && (record.getObjValAs? Bool "resourcesSettled").toOption == some true do
        throw "process resolution requires operator provenance and settled-resource assertion"
    return ← resolve cursor id resolution
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
    let uncertain := match node.1 with
      | .tool _ => match (fromJson? observation : Except String (ToolObservation ToolResult)) with
        | .ok (.interrupted _) | .ok (.uncertain _) => true
        | _ => false
      | _ => false
    return {state := node.2 reply, suspended := if uncertain then some cursor.state else none, editWitness := if uncertain then cursor.editWitness else none}
  | "terminal" =>
    if cursor.pending then throw "terminal record with unresolved intent"
    match node.1 with
    | .finish outcome =>
      let saved ← record.getObjVal? "outcome"
      if saved.compress != (toJson outcome).compress then throw "terminal outcome mismatch"
      return { cursor with terminal := true }
    | _ => throw "premature terminal record"
  | _ => throw "unknown journal record"

def replay (initial : State) (records : List Json) : Except String Cursor :=
  records.foldlM applyRecord { state := initial }

/-- Replay is deterministic for the same initial state and valid record sequence. -/
theorem replay_deterministic (s : State) (records : List Json) (a b : Cursor)
    (ha : replay s records = .ok a) (hb : replay s records = .ok b) : a = b := by
  have h : (Except.ok a : Except String Cursor) = .ok b := ha.symm.trans hb
  exact Except.ok.inj h

end Harness.Recovery
