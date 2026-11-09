import Harness.Proofs.CoreValid
import Harness.Proofs.TurnFrames
import Harness.Proofs.Progress
import Harness.Proofs.OperationIdentity

/-! Follow-up turns retain session authority and spent resources while extending
the closed transcript. Ordinary execution has its existing decreasing rank;
trusted new input begins a new segment and does not replenish the session budget. -/
namespace Harness
variable {app : Application}

theorem begin_turn_core_valid (config : Config) (before after : State app) (task : String)
    (valid : CoreValid config before) (accepted : beginTurn before task = .ok after) :
    CoreValid config after := by
  rw [(begin_turn_contract before after task accepted).1]
  refine ⟨valid.frozen, valid.budgets, ?_, ?_, by trivial, valid.artifacts, valid.repairs⟩
  · simpa [CallsValid, pendingCalls, turnCandidate] using valid.calls.1
  · have ids : retainedResultIds (turnCandidate before task).history = retainedResultIds before.history := by
      simp [turnCandidate, retainedResultIds, List.flatMap_append]
    refine ⟨ids ▸ valid.results.1, ?_⟩
    intro id member
    exact ⟨(valid.results.2 id (ids ▸ member)).1, by simp [turnCandidate, pendingCalls]⟩

theorem begin_turn_closed_history (before after : State app) (task : String)
    (accepted : beginTurn before task = .ok after) : historyValid after.history = true := by
  obtain ⟨equal, _, closed, _⟩ := begin_turn_contract before after task accepted
  rw [equal]
  exact closed_history_append_text before.history task closed

theorem begin_turn_preserves_retirement (before after : State app) (task id : String)
    (accepted : beginTurn before task = .ok after) (retired : RetiredCall id before) :
    RetiredCall id after := by
  rw [(begin_turn_contract before after task accepted).1]
  exact ⟨retired.1, by simp [turnCandidate, pendingCalls]⟩

theorem cancelled_control_settles_undispatched (state : State app) (calls : List (Call app))
    (observation : ControlObservation) (cancelled : observation.cancelled = true) :
    retainedResultIds (consumeControl state (some calls) observation).history =
      retainedResultIds state.history ++ calls.map (·.id) ∧
    (consumeControl state (some calls) observation).phase = .stopped .cancelled ∧
    (consumeControl state (some calls) observation).toolDispatches = state.toolDispatches ∧
    (consumeControl state (some calls) observation).grant = none := by
  simp only [consumeControl, cancelled, if_true, Option.getD_some]
  exact ⟨cancelCalls_retained_ids state calls, rfl, rfl, rfl⟩

theorem cancelled_approval_settles_undispatched (state : State app) (call : Call app) (rest : List (Call app)) :
    retainedResultIds (consumeApproval state call rest .interrupted).history =
      retainedResultIds state.history ++ (call :: rest).map (·.id) ∧
    (consumeApproval state call rest .interrupted).phase = .stopped .cancelled ∧
    (consumeApproval state call rest .interrupted).toolDispatches = state.toolDispatches ∧
    (consumeApproval state call rest .interrupted).grant = none :=
  ⟨cancelCalls_retained_ids state (call :: rest), rfl, rfl, rfl⟩

/-- The new segment has only the remaining cumulative model allowance. The one
extra credit is its control check; admission still must reserve any next attempt. -/
theorem begin_turn_rank (before after : State app) (task : String)
    (accepted : beginTurn before task = .ok after) :
    executionRank after = (before.config.maxModelAttempts - before.modelAttempts) *
      (4 * before.config.maxBatchCalls + 3) + 1 := by
  rw [(begin_turn_contract before after task accepted).1]
  rfl

theorem continued_turn_reply_bound (before after last : State app) (task : String)
    (accepted : beginTurn before task = .ok after) (events : List (ObservedStep app))
    (trace : ExecutionTrace after events last) :
    events.length ≤ (before.config.maxModelAttempts - before.modelAttempts) *
      (4 * before.config.maxBatchCalls + 3) + 1 := by
  have bound := trace.rank_bound executionRank execution_rank_decreases
  rw [begin_turn_rank before after task accepted] at bound
  omega

end Harness
