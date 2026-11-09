import Harness.Core.Effects

/-!
The executable write-ahead protocol for one harness operation. The interpreter
acknowledges each append before this machine exposes dispatch or the saved reply.
An acknowledgment means durable append under the adapter's filesystem contract;
the pure protocol cannot establish that a physical device honored a flush.

Only the operation description and encoded observations enter the journal. This
short-lived protocol is reconstructed from the harness state after recovery.
-/

namespace Harness.Persistence
open Lean

structure Operation (app : Application) where
  id : Nat
  action : Action app
  witness : Option app.Witness := none

variable {app : Application}

def Operation.intent (op : Operation app) : Json :=
  Json.mkObj [("kind", toJson "intent"), ("id", toJson op.id),
    ("action", actionToJson op.action), ("editWitness", toJson op.witness)]

def Operation.completion (op : Operation app) (reply : Reply op.action) : Json :=
  Json.mkObj [("kind", toJson "completion"), ("id", toJson op.id),
    ("observation", replyToJson op.action reply)]

/-- Errors include uncertain writes. They never authorize further progress. -/
abbrev Acknowledgment := Except String Unit

inductive Phase (op : Operation app) where
  | intent
  | dispatch
  | completion (saved : Reply op.action)
  | committed (saved : Reply op.action)
  | failed (message : String)

inductive Command (op : Operation app) where
  | appendIntent
  | dispatch
  | appendCompletion (saved : Reply op.action)
  | committed (saved : Reply op.action)
  | failed (message : String)

def Observation {op : Operation app} : Command op → Type
  | .appendIntent | .appendCompletion _ => Acknowledgment
  | .dispatch => Except String (Reply op.action)
  | .committed _ | .failed _ => Empty

def Signature (op : Operation app) : PFunctor :=
  { A := Command op, B := Observation }

/-- Consume exactly the decoded value that replay will consume. Lossless JSON
encoding is checked before recording completion; a rejected reply stays pending. -/
def acceptReply (op : Operation app) (reply : Reply op.action) : Phase op :=
  let encoded := replyToJson op.action reply
  match replyFromJson op.action encoded with
  | .error message => .failed message
  | .ok saved =>
    if replyToJson op.action saved == encoded then .completion saved
    else .failed "application observation cannot be serialized losslessly"

/-- One request and its typed acknowledgment. These are the definitions the IO
runner interprets; the proof does not assume an independently ordered event log. -/
def step (op : Operation app) : Phase op → Signature op (Phase op)
  | .intent => ⟨.appendIntent, fun ack => match ack with
      | .ok () => .dispatch
      | .error message => .failed message⟩
  | .dispatch => ⟨.dispatch, fun result => match result with
      | .ok reply => acceptReply op reply
      | .error message => .failed message⟩
  | .completion saved => ⟨.appendCompletion saved, fun ack => match ack with
      | .ok () => .committed saved
      | .error message => .failed message⟩
  | .committed saved => ⟨.committed saved, Empty.elim⟩
  | .failed message => ⟨.failed message, Empty.elim⟩

/-- Administrative records have no external dispatch. Their new logical value
is exposed only after the record's durable acknowledgment. -/
inductive CommitPhase (α : Type) where
  | pending (record : Json) (value : α)
  | committed (value : α)
  | failed (message : String)

inductive CommitCommand (α : Type) where
  | append (record : Json)
  | committed (value : α)
  | failed (message : String)

def CommitObservation {α : Type} : CommitCommand α → Type
  | .append _ => Acknowledgment
  | .committed _ | .failed _ => Empty

def CommitSignature (α : Type) : PFunctor :=
  { A := CommitCommand α, B := CommitObservation }

def commitStep {α : Type} : CommitPhase α → CommitSignature α (CommitPhase α)
  | .pending record value => ⟨.append record, fun ack => match ack with
      | .ok () => .committed value
      | .error message => .failed message⟩
  | .committed value => ⟨.committed value, Empty.elim⟩
  | .failed message => ⟨.failed message, Empty.elim⟩

end Harness.Persistence
