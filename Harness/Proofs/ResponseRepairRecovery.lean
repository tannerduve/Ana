import Harness.Proofs.AdministrativeLedger
import Harness.Proofs.RecordFrames

/-! Recovery cannot restore a consumed response-repair allowance. The current
cursor's exact uncertain-continuation witness ties any saved tool position to its
current counter. These statements concern accepted pure recovery, not storage IO. -/
namespace Harness

variable {app : Application}

/-- Replies used by administrative recovery cannot perform a response repair. -/
def RepairNeutralReply : (action : (Action app)) → Reply action → Bool
  | .model _, .uncertain _ => true
  | .model _, _ => false
  | _, _ => true

private def RepairFrameNode (state : (State app)) (node : (HarnessF app) (State app)) : Prop :=
  ∀ response : Reply node.1, RepairNeutralReply node.1 response = true →
    (node.2 response).responseRepairs = state.responseRepairs

theorem repair_neutral_reply_preserves_count (state : (State app)) :
    ∀ response : Reply (step state).1, RepairNeutralReply (step state).1 response = true →
      ((step state).2 response).responseRepairs = state.responseRepairs := by
  change RepairFrameNode state (step state)
  cases phase : state.phase <;> simp only [step, phase]
  case stopped outcome => intro response; exact response.elim
  case controlModel =>
    intro response _
    simp only [advance, consumeControl]
    repeat' first | rfl | split | unfold admitModel | (unfold admitTask; dsimp only) | unfold admitSummary
  case controlTools calls =>
    intro response _
    simp only [advance, consumeControl]
    repeat' first | rfl | contradiction | split | unfold admitTool
  case ask call remaining => intro response _; cases response <;> rfl
  case waiting delay => intro response _; cases response <;> rfl
  case model =>
    by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts)) = true
    · erw [if_pos admitted]; intro response neutral
      cases response <;> simp only [RepairNeutralReply, Bool.false_eq_true] at neutral
      simp only [advance, consumeModel]
      unfold retryOrStop; split <;> rfl
    · erw [if_neg admitted]; intro response; exact response.elim
  case summary =>
    cases pending : state.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts) && planValid state plan) = true
      · erw [if_pos admitted]; intro response _
        exact summary_responseRepairs state plan response
      · erw [if_neg admitted]; intro response; exact response.elim
  case tool call remaining =>
    by_cases admitted : (authorized state.config state.grant call && artifactAuthorized state call && decide (0 < state.toolDispatches) && decide (state.toolDispatches ≤ state.config.maxToolCalls)) = true
    · erw [if_pos admitted]; intro response _
      exact tool_responseRepairs state call remaining (response.map (app.render call.operation))
    · erw [if_neg admitted]; intro response; exact response.elim

theorem uncertain_reply_preserves_repair_count (state : (State app)) (response : Reply (step state).1)
    (uncertain : Recovery.replyIsUncertain (step state).1 response = true) :
    ((step state).2 response).responseRepairs = state.responseRepairs := by
  apply repair_neutral_reply_preserves_count state response
  have neutral : ∀ (action : (Action app)) (reply : Reply action),
      Recovery.replyIsUncertain action reply = true → RepairNeutralReply action reply = true := by
    intro action reply uncertain
    cases action <;> cases reply <;> simp_all [Recovery.replyIsUncertain, RepairNeutralReply]
  exact neutral _ response uncertain

end Harness
namespace Harness.Recovery

variable {app : Application}
open ExceptRules

theorem checked_target_current_repair_count (config : Config) (cursor : (Cursor app)) (prior : (State app))
    (valid : CursorCoreValid config cursor) (accepted : checkedTarget cursor = .ok prior) :
    prior.responseRepairs = cursor.state.responseRepairs := by
  by_cases pending : cursor.pending = true
  · by_cases invalid : (cursor.terminal || cursor.suspended.isSome) = true
    · simp [checkedTarget, pending, invalid] at accepted
    · have equal : cursor.state = prior := by simpa [checkedTarget, pending, invalid] using accepted
      cases equal; rfl
  · cases saved : cursor.suspended with
    | none => simp [checkedTarget, pending, saved] at accepted
    | some old =>
      obtain ⟨_, response, uncertain, current⟩ := valid.suspended old saved
      have ledger := uncertain_reply_preserves_repair_count old response uncertain
      rw [← current] at ledger
      simp only [checkedTarget, pending, Bool.false_eq_true, ↓reduceIte, saved] at accepted
      split at accepted
      · cases action : (step old).1 <;> simp only [action] at accepted
        all_goals simp at accepted
        rw [← accepted]
        exact ledger.symm
      · simp at accepted

theorem recovery_target_repair_count (cursor next : (Cursor app)) (prior : (State app)) (id : Nat)
    (disposition : Disposition) (target : checkedTarget cursor = .ok prior)
    (accepted : recover cursor id disposition = .ok next) :
    next.state.responseRepairs = prior.responseRepairs := by
  by_cases same : id = prior.nextId
  · subst id
    cases node : step prior with
    | mk action continuation =>
      have frame : ∀ response : Reply action, RepairNeutralReply action response = true →
          (continuation response).responseRepairs = prior.responseRepairs := by
        have preserved : RepairFrameNode prior (step prior) := repair_neutral_reply_preserves_count prior
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
        | rfl
        | (exact frame _ rfl)
  · simp [recover, target, same] at accepted

theorem resolution_target_repair_count (cursor next : (Cursor app)) (prior : (State app)) (id : Nat)
    (resolution : app.Resolution) (target : checkedTarget cursor = .ok prior)
    (accepted : resolve cursor id resolution = .ok next) :
    next.state.responseRepairs = prior.responseRepairs := by
  obtain ⟨response, result, _, call, emitted⟩ := resolve_continuation cursor next prior id resolution target accepted
  subst next
  apply repair_neutral_reply_preserves_count prior response
  have neutral : ∀ (action : (Action app)) (reply : Reply action) (call : (Call app)),
      action = .tool call → RepairNeutralReply action reply = true := by
    intro action reply call equal
    cases equal
    rfl
  exact neutral _ response call emitted

theorem recovery_preserves_current_repair_count (config : Config) (cursor next : (Cursor app)) (id : Nat)
    (disposition : Disposition) (valid : CursorCoreValid config cursor)
    (accepted : recover cursor id disposition = .ok next) :
    next.state.responseRepairs = cursor.state.responseRepairs := by
  cases target : checkedTarget cursor with
  | error message => simp [recover, target] at accepted
  | ok prior =>
    exact (recovery_target_repair_count cursor next prior id disposition target accepted).trans
      (checked_target_current_repair_count config cursor prior valid target)

theorem resolution_preserves_current_repair_count (config : Config) (cursor next : (Cursor app)) (id : Nat)
    (resolution : app.Resolution) (valid : CursorCoreValid config cursor)
    (accepted : resolve cursor id resolution = .ok next) :
    next.state.responseRepairs = cursor.state.responseRepairs := by
  cases target : checkedTarget cursor with
  | error message => simp [resolve, target] at accepted
  | ok prior =>
    exact (resolution_target_repair_count cursor next prior id resolution target accepted).trans
      (checked_target_current_repair_count config cursor prior valid target)

/-- No accepted record, including recovery or resolution, can restore repair credit. -/
theorem apply_record_repairs_monotone (config : Config) (cursor next : (Cursor app)) (record : Lean.Json)
    (valid : CursorCoreValid config cursor) (accepted : applyRecord cursor record = .ok next) :
    cursor.state.responseRepairs ≤ next.state.responseRepairs := by
  obtain ⟨kind, decoded, known⟩ := accepted_record_kind_known cursor next record accepted
  simp only [List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with rfl | rfl | rfl | rfl | rfl | rfl
  · have same := (accepted_intent_frame cursor next record decoded accepted).2.1
    rw [same]
  · obtain ⟨_, response, _, _, _, result⟩ := accepted_completion_frame cursor next record decoded accepted
    subst next
    exact (response_repair_count_step cursor.state valid.current.repairs response).1
  · have same := (accepted_terminal_frame cursor next record decoded accepted).1
    rw [same]
  · obtain ⟨id, disposition, recovered⟩ := accepted_recovery_frame cursor next record decoded accepted
    rw [recovery_preserves_current_repair_count config cursor next id disposition valid recovered]
  · obtain ⟨id, resolution, resolved⟩ := accepted_resolution_frame cursor next record decoded accepted
    rw [resolution_preserves_current_repair_count config cursor next id resolution valid resolved]
  · obtain ⟨id, turn, task, accepted⟩ := accepted_user_turn_frame cursor next record decoded accepted
    obtain ⟨_, _, _, _, _, _, begun, _⟩ := new_turn_contract cursor next id turn task accepted
    rw [(begin_turn_contract cursor.state next.state task begun).1]
    exact Nat.le_refl _

/-- The actual record fold retains a nonzero consumed allowance across arbitrary
accepted ordinary/administrative prefixes; it does not assume a trusted checkpoint. -/
theorem record_prefix_repairs_monotone (config : Config) (cursor next : (Cursor app))
    (records : List Lean.Json) (valid : CursorCoreValid config cursor)
    (accepted : records.foldlM applyRecord cursor = .ok next) :
    cursor.state.responseRepairs ≤ next.state.responseRepairs := by
  induction records generalizing cursor with
  | nil =>
    simp only [List.foldlM_nil, pure_ok, Except.ok.injEq] at accepted
    cases accepted
    exact Nat.le_refl _
  | cons record rest ih =>
    simp only [List.foldlM_cons] at accepted
    cases first : applyRecord cursor record with
    | error message => simp [first] at accepted
    | ok middle =>
      simp only [first, ok_bind] at accepted
      exact (apply_record_repairs_monotone config cursor middle record valid first).trans
        (ih middle (apply_record_core_valid config cursor middle record valid first) accepted)

end Harness.Recovery
