import Harness.Core.Transition

/-! Exact frames for bounded task-response repair. Rejected tool calls never enter
accepted history or the pending queue. Fixed feedback is plain user text, and
repairs preserve existing model/tool reservations and the separate retry ledger. -/
namespace Harness

variable {app : Application}

@[simp] theorem repair_config (s : (State app)) (kind : ResponseRepairKind) (message : String) :
    (repairTaskResponse s kind message).config = s.config := by
  unfold repairTaskResponse; split <;> rfl
@[simp] theorem repair_modelAttempts (s : (State app)) (kind : ResponseRepairKind) (message : String) :
    (repairTaskResponse s kind message).modelAttempts = s.modelAttempts := by
  unfold repairTaskResponse; split <;> rfl
@[simp] theorem repair_toolDispatches (s : (State app)) (kind : ResponseRepairKind) (message : String) :
    (repairTaskResponse s kind message).toolDispatches = s.toolDispatches := by
  unfold repairTaskResponse; split <;> rfl
@[simp] theorem repair_retryCount (s : (State app)) (kind : ResponseRepairKind) (message : String) :
    (repairTaskResponse s kind message).retryCount = s.retryCount := by
  unfold repairTaskResponse; split <;> rfl
@[simp] theorem repair_seenCallIds (s : (State app)) (kind : ResponseRepairKind) (message : String) :
    (repairTaskResponse s kind message).seenCallIds = s.seenCallIds := by
  unfold repairTaskResponse; split <;> rfl
@[simp] theorem repair_artifacts (s : (State app)) (kind : ResponseRepairKind) (message : String) :
    (repairTaskResponse s kind message).artifacts = s.artifacts := by
  unfold repairTaskResponse; split <;> rfl
@[simp] theorem repair_grant (s : (State app)) (kind : ResponseRepairKind) (message : String) :
    (repairTaskResponse s kind message).grant = none := by
  unfold repairTaskResponse; split <;> rfl

set_option maxRecDepth 8192 in
/-- All feedback text is fixed and bounded independently of untrusted diagnostics. -/
theorem response_repair_feedback_bounded (kind : ResponseRepairKind) :
    (responseRepairText kind).utf8ByteSize ≤ 1024 := by
  cases kind <;> decide

/-- A successful repair appends exactly one plain feedback message; exhaustion
preserves prior history and the repair count. No rejected assistant blocks occur. -/
theorem repair_state_frame (s : (State app)) (kind : ResponseRepairKind) (message : String) :
    ((repairTaskResponse s kind message).phase = .controlModel ∧
      (repairTaskResponse s kind message).history = s.history ++ [responseRepairMessage kind] ∧
      (repairTaskResponse s kind message).responseRepairs = s.responseRepairs + 1) ∨
    ((repairTaskResponse s kind message).phase = .stopped (.failure message) ∧
      (repairTaskResponse s kind message).history = s.history ∧
      (repairTaskResponse s kind message).responseRepairs = s.responseRepairs) := by
  unfold repairTaskResponse; split
  · exact Or.inl ⟨rfl,rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl,rfl⟩

theorem repair_count_monotone (s : (State app)) (kind : ResponseRepairKind) (message : String) :
    s.responseRepairs ≤ (repairTaskResponse s kind message).responseRepairs := by
  unfold repairTaskResponse; split <;> simp [stop]

theorem repair_count_bounded (s : (State app)) (kind : ResponseRepairKind) (message : String)
    (bounded : s.responseRepairs ≤ s.config.maxResponseRepairs) :
    (repairTaskResponse s kind message).responseRepairs ≤ s.config.maxResponseRepairs := by
  unfold repairTaskResponse; split
  · rename_i admitted
    simp only [Bool.and_eq_true, decide_eq_true_eq] at admitted
    exact admitted.1
  · exact bounded

@[simp] theorem repair_not_tool_batch (s : (State app)) (kind : ResponseRepairKind) (message : String)
    (calls : List (Call app)) : (repairTaskResponse s kind message).phase ≠ .controlTools calls := by
  unfold repairTaskResponse; split <;> simp [stop]

/-- A failed whole-batch check follows the bounded repair policy without accepting
any prefix of the proposed batch. The original complete response remains an observation. -/
theorem invalid_batch_repair_state (state : (State app)) (response : ModelResponse) (message : String)
    (toolUse : response.stop = .toolUse) (consistent : validateModelResponse response = .ok ())
    (rejected : validateBatch state.config state.seenCallIds response.calls app = .error message) :
    consumeModel state (.success response) =
      repairTaskResponse (accountUsage state response.usage) .invalidBatch s!"invalid tool batch: {message}" := by
  cases usage : response.usage <;>
    simp [consumeModel, toolUse, consistent, accountUsage, usage, rejected]

/-- Repair itself can only request control or finish; it cannot directly emit a
new model or tool operation, even before reachability assumptions are introduced. -/
theorem repair_next_action (state : (State app)) (kind : ResponseRepairKind) (message : String) :
    (step (advance (repairTaskResponse state kind message))).1 = .control ∨
    (step (advance (repairTaskResponse state kind message))).1 = .finish (.failure message) := by
  unfold repairTaskResponse; split <;> simp [advance, step, stop]

end Harness
