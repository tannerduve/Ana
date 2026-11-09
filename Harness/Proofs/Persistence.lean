import Harness.Core.Persistence
import Harness.Theory.Coalgebra

/-!
Write-ahead guarantees about the protocol interpreted by `Runner`. Traces record
typed persistence acknowledgments, including failures. The filesystem meaning
of a successful acknowledgment remains an adapter contract. No premise assumes
that the event trace is already ordered correctly.
-/

namespace Harness.Persistence
open Lean PFunctor.Coalgebra

variable {app : Application} (op : Operation app)

inductive Event (op : Operation app) where
  | intent (ack : Acknowledgment)
  | dispatched
  | completion (saved : Reply op.action) (ack : Acknowledgment)

def observe (phase : Phase op) : Observation (step op phase).1 → Event op :=
  match phase with
  | .intent => fun ack => .intent ack
  | .dispatch => fun _ => .dispatched
  | .completion saved => fun ack => .completion saved ack
  | .committed _ | .failed _ => Empty.elim

/-- Evidence accumulated before exposing each protocol stage. -/
def Ready (phase : Phase op) (events : List (Event op)) : Prop :=
  match phase with
  | .intent | .failed _ => True
  | .dispatch => .intent (.ok ()) ∈ events
  | .completion _ => .intent (.ok ()) ∈ events ∧ .dispatched ∈ events
  | .committed saved => .intent (.ok ()) ∈ events ∧ .dispatched ∈ events ∧
      .completion saved (.ok ()) ∈ events

private theorem acceptReply_ready (reply : Reply op.action) (events : List (Event op))
    (intent : Event.intent (.ok ()) ∈ events) (dispatched : Event.dispatched ∈ events) :
    Ready op (acceptReply op reply) events := by
  unfold acceptReply
  dsimp only
  split
  · trivial
  · split
    · exact ⟨intent, dispatched⟩
    · trivial

theorem ready_preserved (phase : Phase op) (events : List (Event op))
    (ready : Ready op phase events) (reply : Observation (step op phase).1) :
    Ready op ((step op phase).2 reply) (events ++ [observe op phase reply]) := by
  cases phase with
  | intent => cases reply <;> simp [step, observe, Ready]
  | dispatch =>
    cases reply with
    | error message => trivial
    | ok result =>
      apply acceptReply_ready
      · exact List.mem_append_left _ ready
      · simp [observe]
  | completion saved =>
    cases reply with
    | error message => trivial
    | ok acknowledgment =>
      rcases acknowledgment with ⟨⟩
      exact ⟨List.mem_append_left _ ready.1, List.mem_append_left _ ready.2,
        by simp [observe]⟩
  | committed saved => exact reply.elim
  | failed message => exact reply.elim

theorem trace_ready {first last : Phase op} {events earlier : List (Event op)}
    (trace : Trace (step op) (observe op) first events last)
    (ready : Ready op first earlier) : Ready op last (earlier ++ events) := by
  induction trace generalizing earlier with
  | nil => simpa using ready
  | cons phase reply tail ih =>
    have next := ready_preserved op phase earlier ready reply
    simpa [List.append_assoc] using ih next

/-- Every dispatch exposed by a reachable protocol earlier has a prior successful
acknowledgment for this exact operation's intent. -/
theorem dispatch_has_durable_intent {events : List (Event op)}
    (trace : Trace (step op) (observe op) .intent events .dispatch) :
    Event.intent (.ok ()) ∈ events := by
  simpa [Ready] using trace_ready op trace (earlier := []) trivial

/-- The reply released to the harness has its own earlier durable completion,
in addition to the intent and dispatch. -/
theorem committed_has_durable_completion {events : List (Event op)}
    {saved : Reply op.action}
    (trace : Trace (step op) (observe op) .intent events (.committed saved)) :
    Event.intent (.ok ()) ∈ events ∧ Event.dispatched ∈ events ∧
      Event.completion saved (.ok ()) ∈ events := by
  simpa [Ready] using trace_ready op trace (earlier := []) trivial

theorem failed_has_no_continuation (message : String) :
    ¬ ∃ next, Next (step op) (.failed message) next := by
  rintro ⟨next, reply, _⟩
  exact reply.elim

theorem intent_failure_stops (message : String) :
    (step op .intent).2 (.error message) = .failed message := rfl

theorem completion_failure_stops (saved : Reply op.action) (message : String) :
    (step op (.completion saved)).2 (.error message) = .failed message := rfl

def rank : Phase op → Nat
  | .intent => 3
  | .dispatch => 2
  | .completion _ => 1
  | .committed _ | .failed _ => 0

private theorem accepted_reply_rank (reply : Reply op.action) :
    rank op (acceptReply op reply) < 2 := by
  unfold acceptReply
  dsimp only
  split
  · simp [rank]
  · split <;> simp [rank]

theorem rank_decreases (phase : Phase op) (reply : Observation (step op phase).1) :
    rank op ((step op phase).2 reply) < rank op phase := by
  cases phase with
  | intent => cases reply <;> simp [step, rank]
  | dispatch =>
    cases reply with
    | error message => simp [step, rank]
    | ok saved => exact accepted_reply_rank op saved
  | completion saved => cases reply <;> simp [step, rank]
  | committed saved => exact reply.elim
  | failed message => exact reply.elim

/-- The IO interpreter's four inspections suffice: at most three acknowledgments
can be consumed, followed by one terminal inspection. -/
theorem reply_bound {events : List (Event op)} {last : Phase op}
    (trace : Trace (step op) (observe op) .intent events last) : events.length ≤ 3 := by
  have bound := trace.rank_bound (rank op) (rank_decreases op)
  change events.length + rank op last ≤ 3 at bound
  omega

/-- Administrative advancement is controlled by the same acknowledgment type;
only success releases its proposed new value. -/
theorem commit_releases_iff {α : Type} (record : Json) (value returned : α)
    (ack : Acknowledgment) :
    (commitStep (.pending record value)).2 ack = .committed returned ↔
      ack = .ok () ∧ value = returned := by
  cases ack with
  | error message => simp [commitStep]
  | ok acknowledgment => cases acknowledgment; simp [commitStep]

theorem commit_failure_stops {α : Type} (record : Json) (value : α) (message : String) :
    (commitStep (.pending record value)).2 (.error message) = .failed message := rfl

end Harness.Persistence
