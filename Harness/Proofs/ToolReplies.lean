import Harness.Core.Transition

/-!
Constructor-based scopes for ordinary tool completion versus the new batch-closing
timeout observation and cancellation that settles an undispatched batch. These predicates classify replies, independently of the state
or of the properties later proved about their continuations.
-/

namespace Harness

def OrdinaryToolReply {α : Type} : ToolObservation α → Prop
  | .timedOut _ => False
  | _ => True

@[simp] theorem ordinary_tool_reply_map {α β : Type} (f : α → β)
    (response : ToolObservation α) : OrdinaryToolReply (response.map f) ↔ OrdinaryToolReply response := by
  cases response <;> rfl

def OrdinaryReply {app : Application} : (action : Action app) → Reply action → Prop
  | .tool _, response => OrdinaryToolReply response
  | .control, response => response.cancelled = false
  | .ask _, .interrupted => False
  | .finish _, response => nomatch response
  | _, _ => True

end Harness
