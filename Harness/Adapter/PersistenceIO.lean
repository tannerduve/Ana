import Harness.Core.Persistence
import Harness.Adapter.JournalIO

/-!
Interpret only the persistence protocol's requests. Policy, the order of requests,
and release of an authoritative reply are decided by `Core.Persistence.step`.
Journal acknowledgments rely on `JournalIO.Writer.append`'s durability contract.
-/

namespace Harness.PersistenceIO
open Lean

private def acknowledge (action : IO Unit) : IO Persistence.Acknowledgment := do
  try action; return .ok ()
  catch error => return .error error.toString

variable {app : Application}

/-- The fixed fuel bounds this protocol interpreter, not the agent's session.
The ordinary successful path is intent, dispatch, completion, committed. -/
private def runOperation (writer : JournalIO.Writer) (op : Persistence.Operation app)
    (execute : IO (Reply op.action)) (event : String → Json → IO Unit)
    (phase : Persistence.Phase op) : Nat → IO (Reply op.action)
  | 0 => throw <| IO.userError "persistence protocol exhausted its internal bound"
  | fuel + 1 => do
    let node := Persistence.step op phase
    match node with
    | ⟨.appendIntent, next⟩ =>
      let ack ← acknowledge (writer.append op.intent)
      if let .ok () := ack then event "intent" (actionToJson op.action)
      runOperation writer op execute event (next ack) fuel
    | ⟨.dispatch, next⟩ =>
      let result : Except String (Reply op.action) ←
        try pure (.ok (← execute)) catch error => pure (.error error.toString)
      runOperation writer op execute event (next result) fuel
    | ⟨.appendCompletion saved, next⟩ =>
      let ack ← acknowledge (writer.append (op.completion saved))
      if let .ok () := ack then event "completion" (replyToJson op.action saved)
      runOperation writer op execute event (next ack) fuel
    | ⟨.committed saved, _⟩ => pure saved
    | ⟨.failed message, _⟩ => throw <| IO.userError message

def operation (writer : JournalIO.Writer) (op : Persistence.Operation app)
    (execute : IO (Reply op.action)) (event : String → Json → IO Unit) : IO (Reply op.action) :=
  runOperation writer op execute event .intent 4

private def runCommit (writer : JournalIO.Writer) (phase : Persistence.CommitPhase α) : Nat → IO α
  | 0 => throw <| IO.userError "commit protocol exhausted its internal bound"
  | fuel + 1 => do
    let node := Persistence.commitStep phase
    match node with
    | ⟨.append record, next⟩ =>
      let ack ← acknowledge (writer.append record)
      runCommit writer (next ack) fuel
    | ⟨.committed value, _⟩ => pure value
    | ⟨.failed message, _⟩ => throw <| IO.userError message

/-- Initial, terminal, recovery, resolution and user-turn records share the
proved rule: a proposed value is released only after its durable append. -/
def commit (writer : JournalIO.Writer) (record : Json) (value : α) : IO α :=
  runCommit writer (.pending record value) 2

end Harness.PersistenceIO
