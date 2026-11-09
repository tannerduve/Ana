import Harness.Core.Transition

/-! Pure replay of completed typed observations. Storage checksums and fsync remain IO contracts. -/
namespace Harness.Recovery
open Lean

structure Cursor where
  state : State
  pending : Bool := false
  terminal : Bool := false

/-- Records are ordered by the framed journal; an intent must match the next executable action. -/
def applyRecord (cursor : Cursor) (record : Json) : Except String Cursor := do
  if cursor.terminal then throw "record after terminal outcome"
  let kind ← record.getObjValAs? String "kind"
  let id ← record.getObjValAs? Nat "id"
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
    | _ => return { cursor with pending := true }
  | "completion" =>
    if !cursor.pending then throw "completion without intent"
    let observation ← record.getObjVal? "observation"
    let reply ← replyFromJson node.1 observation
    return { state := node.2 reply }
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
