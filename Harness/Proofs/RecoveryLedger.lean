import Harness.Proofs.Except
import Harness.Proofs.CoreValid

namespace Harness

variable {app : Application}

/-- Reservations are retained exactly, rather than merely remaining below their
ceilings. This relation does not assert provider token/cost accounting. -/
def SameReservations (before after : (State app)) : Prop :=
  after.modelAttempts = before.modelAttempts ∧ after.toolDispatches = before.toolDispatches

private theorem model_reservations (state : (State app)) (observation : ModelObservation) :
    SameReservations state (consumeModel state observation) := by
  cases observation with
  | interrupted => exact ⟨rfl, rfl⟩
  | uncertain message => simp only [consumeModel]; unfold retryOrStop; split <;> exact ⟨rfl, rfl⟩
  | failure kind message =>
    cases kind <;> simp only [consumeModel]
    all_goals first | exact ⟨rfl, rfl⟩ | (solve | simp [SameReservations]) | (unfold retryOrStop; split <;> exact ⟨rfl, rfl⟩)
  | success response =>
    cases usage : response.usage <;> cases reason : response.stop <;>
      simp only [consumeModel, reason, usage, accountUsage]
    all_goals repeat' first | (exact ⟨rfl, rfl⟩) | (solve | simp [SameReservations]) | split

private theorem summary_reservations (state : (State app)) (plan : SummaryPlan) (observation : ModelObservation) :
    SameReservations state (consumeSummary state plan observation) := by
  cases observation with
  | interrupted => exact ⟨rfl, rfl⟩
  | uncertain message => simp only [consumeSummary]; unfold retryOrStop; split <;> exact ⟨rfl, rfl⟩
  | failure kind message =>
    cases kind <;> simp only [consumeSummary]
    all_goals first | exact ⟨rfl, rfl⟩ | (unfold retryOrStop; split <;> exact ⟨rfl, rfl⟩)
  | success response =>
    cases usage : response.usage <;> cases reason : response.stop <;>
      simp only [consumeSummary, reason, usage, accountUsage]
    all_goals repeat' first | (exact ⟨rfl, rfl⟩) | split | (unfold installSummary; dsimp only)

theorem tool_reservations (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ToolObservation ToolResult) : SameReservations state (consumeTool state call remaining observation) := by
  cases observation <;> simp only [consumeTool, retainPartialArtifacts]
  all_goals repeat' first | (exact ⟨rfl, rfl⟩) | split

private def ReservationNode (state : (State app)) (node : (HarnessF app) (State app)) : Prop :=
  ∀ response : Reply node.1, node.1 ≠ .control → SameReservations state (node.2 response)

/-- Reservation admission occurs at control transitions. Every returned model,
summary, tool, approval or wait observation retains both existing counters. -/
theorem noncontrol_reservations (state : (State app)) :
    ∀ response : Reply (step state).1, (step state).1 ≠ .control →
      SameReservations state ((step state).2 response) := by
  change ReservationNode state (step state)
  cases phase : state.phase <;> simp only [step, phase]
  case stopped outcome => intro response; exact response.elim
  case controlModel => intro response impossible; exact (impossible rfl).elim
  case controlTools calls => intro response impossible; exact (impossible rfl).elim
  case ask call remaining => intro response _; cases response <;> exact ⟨rfl, rfl⟩
  case waiting delay => intro response _; cases response <;> exact ⟨rfl, rfl⟩
  case model =>
    by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts)) = true
    · erw [if_pos admitted]; exact fun response _ => model_reservations state response
    · erw [if_neg admitted]; intro response; exact response.elim
  case summary =>
    cases pending : state.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts) && planValid state plan) = true
      · erw [if_pos admitted]; exact fun response _ => summary_reservations state plan response
      · erw [if_neg admitted]; intro response; exact response.elim
  case tool call remaining =>
    by_cases admitted : (authorized state.config state.grant call && artifactAuthorized state call && decide (0 < state.toolDispatches) && decide (state.toolDispatches ≤ state.config.maxToolCalls)) = true
    · erw [if_pos admitted]; exact fun response _ => tool_reservations state call remaining (response.map (app.render call.operation))
    · erw [if_neg admitted]; intro response; exact response.elim

theorem uncertain_reply_reservations (state : (State app)) (response : Reply (step state).1)
    (uncertain : Recovery.replyIsUncertain (step state).1 response = true) :
    SameReservations state ((step state).2 response) := by
  apply noncontrol_reservations state response
  intro control
  have impossible : ∀ (action : (Action app)) (reply : Reply action),
      action = .control → Recovery.replyIsUncertain action reply = false := by
    intro action reply equal
    cases equal
    rfl
  have falseReply := impossible _ response control
  simp [falseReply] at uncertain

/-- An ordinary settled tool reply removes exactly the head of its admitted queue, without
reordering or regenerating any later call. -/
theorem settled_tool_queue (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (response : ToolObservation (app.Result call.operation))
    (settled : Recovery.replyIsUncertain (.tool call) response = false)
    (ordinary : OrdinaryToolReply response) :
    (consumeTool state call remaining (response.map (app.render call.operation))).phase = .controlTools remaining := by
  cases response <;> simp only [Recovery.replyIsUncertain] at settled
  all_goals simp only [ToolObservation.map]
  all_goals simp only [OrdinaryToolReply] at ordinary
  all_goals try contradiction
  all_goals simp only [consumeTool]
  all_goals repeat' first | rfl | split

theorem emitted_tool_phase (state : (State app)) (call : (Call app))
    (emitted : (step state).1 = .tool call) :
    ∃ remaining, state.phase = .tool call remaining := by
  cases phase : state.phase <;> simp only [step, phase] at emitted
  all_goals try contradiction
  case model =>
    by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts)) = true
    · simp only [admitted] at emitted; contradiction
    · simp only [admitted] at emitted; contradiction
  case summary =>
    cases pending : state.pendingSummary with
    | none => simp [pending] at emitted
    | some plan =>
      simp only [pending] at emitted
      by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts) && planValid state plan) = true
      · simp only [admitted] at emitted; contradiction
      · simp only [admitted] at emitted; contradiction
  case tool proposed remaining =>
    by_cases admitted : (authorized state.config state.grant proposed && artifactAuthorized state proposed && decide (0 < state.toolDispatches) && decide (state.toolDispatches ≤ state.config.maxToolCalls)) = true
    · simp only [admitted] at emitted
      cases emitted
      exact ⟨remaining, rfl⟩
    · simp only [admitted] at emitted; contradiction

private def ToolQueueNode (state : (State app)) (node : (HarnessF app) (State app)) : Prop :=
  ∀ (response : Reply node.1) (call : (Call app)), node.1 = .tool call →
    Recovery.replyIsUncertain node.1 response = false →
    OrdinaryReply node.1 response →
    ∃ remaining, state.phase = .tool call remaining ∧ (node.2 response).phase = .controlTools remaining

theorem emitted_settled_tool_queue (state : (State app)) :
    ∀ (response : Reply (step state).1) (call : (Call app)), (step state).1 = .tool call →
      Recovery.replyIsUncertain (step state).1 response = false →
      OrdinaryReply (step state).1 response →
      ∃ remaining, state.phase = .tool call remaining ∧
        ((step state).2 response).phase = .controlTools remaining := by
  change ToolQueueNode state (step state)
  cases phase : state.phase <;> simp only [step, phase]
  case stopped outcome => intro response; exact response.elim
  case controlModel => simp [ToolQueueNode]
  case controlTools calls => simp [ToolQueueNode]
  case ask call remaining => simp [ToolQueueNode]
  case waiting delay => simp [ToolQueueNode]
  case model =>
    by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts)) = true
    · erw [if_pos admitted]; simp [ToolQueueNode]
    · erw [if_neg admitted]; intro response; exact response.elim
  case summary =>
    cases pending : state.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts) && planValid state plan) = true
      · erw [if_pos admitted]; simp [ToolQueueNode]
      · erw [if_neg admitted]; intro response; exact response.elim
  case tool call remaining =>
    by_cases admitted : (authorized state.config state.grant call && artifactAuthorized state call && decide (0 < state.toolDispatches) && decide (state.toolDispatches ≤ state.config.maxToolCalls)) = true
    · erw [if_pos admitted]
      intro response proposed equal settled ordinary
      cases equal
      exact ⟨remaining, phase, settled_tool_queue state call remaining response settled ordinary⟩
    · erw [if_neg admitted]; intro response; exact response.elim

end Harness

namespace Harness.Recovery

variable {app : Application}

open ExceptRules

/-- Successful resolution uses the recorded tool's actual continuation. The
result is a fresh cursor, so a second resolution cannot reuse its saved position. -/
theorem resolve_ordinary_continuation (cursor next : (Cursor app)) (prior : (State app)) (id : Nat) (resolution : app.Resolution)
    (target : checkedTarget cursor = .ok prior)
    (accepted : resolve cursor id resolution = .ok next) :
    ∃ response : Reply (step prior).1,
      next = {state := (step prior).2 response} ∧ replyIsUncertain (step prior).1 response = false ∧
        OrdinaryReply (step prior).1 response ∧
        ∃ call, (step prior).1 = .tool call := by
  by_cases same : id = prior.nextId
  · subst id
    cases node : step prior with
    | mk action continuation =>
      cases action <;> simp only [resolve, target, node, ok_bind,
        beq_self_eq_true, ↓reduceIte, pure_ok, throw_error, error_bind] at accepted
      all_goals try contradiction
      case tool call =>
        obtain ⟨settled, _, accepted⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
        cases settled <;> simp only [Settled.observation, Except.ok.injEq] at accepted
        all_goals cases accepted
        all_goals exact ⟨_, rfl, rfl, trivial, call, rfl⟩
  · simp [resolve, target, same] at accepted

theorem resolve_continuation (cursor next : (Cursor app)) (prior : (State app)) (id : Nat) (resolution : app.Resolution)
    (target : checkedTarget cursor = .ok prior)
    (accepted : resolve cursor id resolution = .ok next) :
    ∃ response : Reply (step prior).1,
      next = {state := (step prior).2 response} ∧ replyIsUncertain (step prior).1 response = false ∧
        ∃ call, (step prior).1 = .tool call := by
  obtain ⟨response, result, settled, _, emitted⟩ :=
    resolve_ordinary_continuation cursor next prior id resolution target accepted
  exact ⟨response, result, settled, emitted⟩

theorem resolution_target_reservations (cursor next : (Cursor app)) (prior : (State app)) (id : Nat)
    (resolution : app.Resolution) (target : checkedTarget cursor = .ok prior)
    (accepted : resolve cursor id resolution = .ok next) : SameReservations prior next.state := by
  obtain ⟨response, result, _, call, emitted⟩ := resolve_continuation cursor next prior id resolution target accepted
  subst next
  exact noncontrol_reservations prior response (by simp [emitted])

private def LedgerNode (prior : (State app)) (node : (HarnessF app) (State app)) : Prop :=
  ∀ response : Reply node.1, node.1 ≠ .control → SameReservations prior (node.2 response)

/-- All successful recovery dispositions retain the already reserved attempts
and calls. Reissuing a control/approval/wait observation never refunds a slot. -/
theorem recovery_target_reservations (cursor next : (Cursor app)) (prior : (State app)) (id : Nat)
    (disposition : Disposition) (target : checkedTarget cursor = .ok prior)
    (accepted : recover cursor id disposition = .ok next) : SameReservations prior next.state := by
  by_cases same : id = prior.nextId
  · subst id
    cases node : step prior with
    | mk action continuation =>
      have frame : ∀ response : Reply action, action ≠ .control → SameReservations prior (continuation response) := by
        have preserved : LedgerNode prior (step prior) := noncontrol_reservations prior
        rw [node] at preserved
        exact preserved
      cases action <;> cases disposition <;>
        simp only [recover, target, node, ok_bind, beq_self_eq_true,
          ↓reduceIte, pure_ok, throw_error, error_bind] at accepted
      all_goals repeat' first
        | (split at accepted)
        | (simp only [pure_ok, throw_error, ok_bind, error_bind,
            bind, Except.bind, Functor.map, Except.map] at accepted)
        | (cases accepted)
        | (exact ⟨rfl, rfl⟩)
        | (exact frame _ (by intro impossible; cases impossible))
  · simp [recover, target, same] at accepted

theorem recover_tool_ordinary_continuation (cursor next : (Cursor app)) (prior : (State app)) (id : Nat)
    (disposition : Disposition) (call : (Call app)) (target : checkedTarget cursor = .ok prior)
    (emitted : (step prior).1 = .tool call) (accepted : recover cursor id disposition = .ok next) :
    ∃ response : Reply (step prior).1,
      next = {state := (step prior).2 response} ∧ replyIsUncertain (step prior).1 response = false ∧
        OrdinaryReply (step prior).1 response := by
  by_cases same : id = prior.nextId
  · subst id
    cases node : step prior with
    | mk action continuation =>
      have selected : action = .tool call := by simpa only [node] using emitted
      cases selected
      cases disposition <;> simp only [recover, target, node, ok_bind, beq_self_eq_true,
        ↓reduceIte, pure_ok, throw_error, error_bind] at accepted
      all_goals repeat' first
        | (split at accepted)
        | (simp only [pure_ok, throw_error, ok_bind, error_bind,
            bind, Except.bind, Functor.map, Except.map] at accepted)
        | (cases accepted)
        | (exact ⟨_, rfl, rfl, trivial⟩)
  · simp [recover, target, same] at accepted

theorem recover_tool_continuation (cursor next : (Cursor app)) (prior : (State app)) (id : Nat)
    (disposition : Disposition) (call : (Call app)) (target : checkedTarget cursor = .ok prior)
    (emitted : (step prior).1 = .tool call) (accepted : recover cursor id disposition = .ok next) :
    ∃ response : Reply (step prior).1,
      next = {state := (step prior).2 response} ∧ replyIsUncertain (step prior).1 response = false := by
  obtain ⟨response, result, settled, _⟩ :=
    recover_tool_ordinary_continuation cursor next prior id disposition call target emitted accepted
  exact ⟨response, result, settled⟩

theorem resolution_preserves_pending_order (cursor next : (Cursor app)) (prior : (State app)) (id : Nat)
    (resolution : app.Resolution) (target : checkedTarget cursor = .ok prior)
    (accepted : resolve cursor id resolution = .ok next) :
    ∃ call remaining, prior.phase = .tool call remaining ∧ next.state.phase = .controlTools remaining := by
  obtain ⟨response, result, settled, ordinary, call, emitted⟩ := resolve_ordinary_continuation cursor next prior id resolution target accepted
  obtain ⟨remaining, before, after⟩ := emitted_settled_tool_queue prior response call emitted settled ordinary
  exact ⟨call, remaining, before, by simpa only [result] using after⟩

theorem recovery_tool_preserves_pending_order (cursor next : (Cursor app)) (prior : (State app)) (id : Nat)
    (disposition : Disposition) (call : (Call app)) (target : checkedTarget cursor = .ok prior)
    (emitted : (step prior).1 = .tool call) (accepted : recover cursor id disposition = .ok next) :
    ∃ remaining, prior.phase = .tool call remaining ∧ next.state.phase = .controlTools remaining := by
  obtain ⟨response, result, settled, ordinary⟩ := recover_tool_ordinary_continuation cursor next prior id disposition call target emitted accepted
  obtain ⟨remaining, before, after⟩ := emitted_settled_tool_queue prior response call emitted settled ordinary
  exact ⟨remaining, before, by simpa only [result] using after⟩

end Harness.Recovery
