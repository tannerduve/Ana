import Harness.Proofs.Except
import Harness.Core.Recovery
import Harness.Proofs.Configuration

namespace Harness.Recovery

variable {app : Application}

open ExceptRules

/-- A restarted control observation has a fresh operation identity, retains every
reservation and history field, and explicitly invalidates any unspent grant. -/
theorem recover_control_lost (cursor : (Cursor app)) (prior : (State app))
    (target : checkedTarget cursor = .ok prior)
    (action : (step prior).1 = .control) :
    recover cursor prior.nextId .controlLost =
      .ok {state := advance {prior with grant := none}} := by
  cases hn : step prior with
  | mk selected continuation =>
    have selected_control : selected = .control := by simpa [hn] using action
    cases selected_control
    simp [recover, target, hn]

/-- An absent answer never becomes approval. Recovery returns to control before
asking again and does not reserve a tool dispatch. -/
theorem recover_approval_lost (cursor : (Cursor app)) (prior : (State app))
    (call : (Call app)) (remaining : List (Call app))
    (target : checkedTarget cursor = .ok prior)
    (phase : prior.phase = .ask call remaining) :
    recover cursor prior.nextId .approvalLost =
      .ok {state := advance {prior with phase := .controlTools (call :: remaining), grant := none}} := by
  simp [recover, target, step, phase]

/-- The elapsed reply is not fabricated: the complete delay is emitted again,
under the next identity, and remains subject to ordinary cancellation. -/
theorem recover_wait_lost (cursor : (Cursor app)) (prior : (State app)) (delay : Nat)
    (target : checkedTarget cursor = .ok prior)
    (phase : prior.phase = .waiting delay) :
    recover cursor prior.nextId .waitLost =
      .ok {state := advance {prior with grant := none}} := by
  simp [recover, target, step, phase]

/-- Losing a task response follows the actual core uncertainty transition. The
recovery layer neither reserves another attempt nor bypasses the retry policy. -/
theorem recover_task_response_lost (cursor : (Cursor app)) (prior : (State app))
    (target : checkedTarget cursor = .ok prior)
    (phase : prior.phase = .model)
    (reserved : 0 < prior.modelAttempts ∧ prior.modelAttempts ≤ prior.config.maxModelAttempts) :
    recover cursor prior.nextId .modelLost = .ok {state := advance (consumeModel prior
      (.uncertain "model response lost during interruption; prior usage is unknown"))} := by
  simp [recover, target, step, phase, reserved.1, reserved.2]

theorem lost_task_response_accounted (s : (State app)) (message : String) :
    (advance (consumeModel s (.uncertain message))).modelAttempts = s.modelAttempts ∧
    (advance (consumeModel s (.uncertain message))).toolDispatches = s.toolDispatches ∧
    (advance (consumeModel s (.uncertain message))).unknownUsage = s.unknownUsage + 1 ∧
    (advance (consumeModel s (.uncertain message))).config = s.config ∧
    (advance (consumeModel s (.uncertain message))).nextId = s.nextId + 1 := by
  simp only [consumeModel]
  unfold retryOrStop
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Losing a summary preserves its plan/view/history and uses the same uncertainty
transition and attempt ledger as a live interrupted transport. -/
theorem recover_summary_response_lost (cursor : (Cursor app)) (prior : (State app)) (plan : SummaryPlan)
    (target : checkedTarget cursor = .ok prior)
    (phase : prior.phase = .summary) (pending : prior.pendingSummary = some plan)
    (reserved : 0 < prior.modelAttempts ∧ prior.modelAttempts ≤ prior.config.maxModelAttempts)
    (valid : planValid prior plan = true) :
    recover cursor prior.nextId .modelLost = .ok {state := advance (consumeSummary prior plan
      (.uncertain "model response lost during interruption; prior usage is unknown"))} := by
  simp [recover, target, step, phase, pending, reserved.1, reserved.2, valid]

theorem lost_summary_response_preserves_context (s : (State app)) (plan : SummaryPlan) (message : String) :
    (consumeSummary s plan (.uncertain message)).history = s.history ∧
    (consumeSummary s plan (.uncertain message)).activeView = s.activeView ∧
    (consumeSummary s plan (.uncertain message)).pendingSummary = s.pendingSummary ∧
    (consumeSummary s plan (.uncertain message)).modelAttempts = s.modelAttempts ∧
    (consumeSummary s plan (.uncertain message)).unknownUsage = s.unknownUsage + 1 := by
  simp only [consumeSummary]
  unfold retryOrStop
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- An already cancelled turn cannot be reopened, even if a caller supplies an
unrelated suspended state. This guard supplements the reachable-cursor invariant. -/
theorem cancelled_cursor_has_no_target (cursor : (Cursor app))
    (pending : cursor.pending = false) (cancelled : cursor.state.phase = .stopped .cancelled) :
    ∃ message, checkedTarget cursor = .error message := by
  cases hs : cursor.suspended <;> simp [checkedTarget, pending, hs, cancelled]

end Harness.Recovery
