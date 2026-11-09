import Harness.Proofs.Configuration
import Harness.Proofs.Trace
import Harness.Proofs.Validation

namespace Harness

variable {app : Application}

/-- The phase exposes only a suffix of one finite admitted tool batch. -/
def QueueBound (s : (State app)) : Prop :=
  match s.phase with
  | .controlTools calls => calls.length ≤ s.config.maxBatchCalls
  | .ask _ remaining | .tool _ remaining => remaining.length + 1 ≤ s.config.maxBatchCalls
  | _ => True

@[simp] theorem queue_advance (s : (State app)) : QueueBound (advance s) = QueueBound s := rfl

theorem queue_admitModel (s : (State app)) : QueueBound (admitModel s) := by
  unfold admitModel
  repeat' first | (solve | simp [QueueBound, stop]) | split | (unfold admitTask; dsimp only) | (unfold admitSummary)

theorem queue_repair (s : (State app)) (kind : ResponseRepairKind) (message : String) :
    QueueBound (repairTaskResponse s kind message) := by
  unfold repairTaskResponse; split <;> trivial

theorem queue_consumeModel (s : (State app)) (observation : ModelObservation) :
    QueueBound (consumeModel s observation) := by
  cases observation with
  | interrupted => trivial
  | uncertain message =>
    simp only [consumeModel]
    unfold retryOrStop
    split <;> trivial
  | failure kind message =>
    cases kind <;> simp only [consumeModel]
    all_goals first | trivial | exact queue_repair _ _ _ | (unfold retryOrStop; split <;> trivial)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeModel, hs, hu, accountUsage]
    all_goals repeat' first | trivial | (exact queue_repair _ _ _) | split
    all_goals
      rename_i calls accepted
      exact (validated_batch_length _ _ _ _ accepted).2

theorem queue_consumeSummary (s : (State app)) (plan : SummaryPlan) (observation : ModelObservation) :
    QueueBound (consumeSummary s plan observation) := by
  cases observation with
  | interrupted => trivial
  | uncertain message =>
    simp only [consumeSummary]
    unfold retryOrStop
    split <;> trivial
  | failure kind message =>
    cases kind <;> simp only [consumeSummary]
    all_goals first | trivial | (unfold retryOrStop; split <;> trivial)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeSummary, hs, hu, accountUsage]
    all_goals repeat' first | trivial | split | (unfold installSummary; dsimp only)

theorem queue_admitTool (s : (State app)) (call : (Call app)) (remaining : List (Call app))
    (bounded : remaining.length + 1 ≤ s.config.maxBatchCalls) :
    QueueBound (admitTool s call remaining) := by
  unfold admitTool
  repeat' first | trivial | split | (simp [QueueBound, appendResult]; omega)

theorem queue_consumeTool (s : (State app)) (call : (Call app)) (remaining : List (Call app))
    (bounded : remaining.length + 1 ≤ s.config.maxBatchCalls) (observation : ToolObservation ToolResult) :
    QueueBound (consumeTool s call remaining observation) := by
  cases observation <;> simp only [consumeTool, retainPartialArtifacts]
  all_goals repeat' first | trivial | split | (simp [QueueBound, appendResult]; omega)

theorem queue_consumeApproval (s : (State app)) (call : (Call app)) (remaining : List (Call app))
    (bounded : remaining.length + 1 ≤ s.config.maxBatchCalls) (observation : ApprovalObservation) :
    QueueBound (consumeApproval s call remaining observation) := by
  cases observation <;> simp [consumeApproval, QueueBound, appendResult, cancelCalls] <;> omega

private def QueueNode (node : (HarnessF app) (State app)) : Prop :=
  ∀ response : Reply node.1, QueueBound (node.2 response)

/-- Every actual typed response preserves the finite admitted-queue bound. -/
theorem queue_preserved (s : (State app)) (bounded : QueueBound s) :
    ∀ response : Reply (step s).fst, QueueBound ((step s).snd response) := by
  change QueueNode (step s)
  cases hp : s.phase <;> simp only [step, hp]
  case stopped outcome => intro response; exact response.elim
  case controlModel =>
    intro response
    simp only [queue_advance, consumeControl]
    split
    · trivial
    · split
      · trivial
      · exact queue_admitModel s
  case controlTools calls =>
    intro response
    simp only [queue_advance, consumeControl]
    split
    · trivial
    · split
      · trivial
      · cases calls with
        | nil => trivial
        | cons call remaining =>
          exact queue_admitTool s call remaining (by simpa [QueueBound, hp] using bounded)
  case ask call remaining =>
    intro response
    exact queue_consumeApproval s call remaining (by simpa [QueueBound, hp] using bounded) response
  case waiting delay =>
    intro response
    cases response <;> trivial
  case model =>
    by_cases admitted : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts)) = true
    · erw [if_pos admitted]; intro response; exact queue_consumeModel s response
    · erw [if_neg admitted]; intro response; exact response.elim
  case summary =>
    cases pending : s.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases admitted : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts) && planValid s plan) = true
      · erw [if_pos admitted]; intro response; exact queue_consumeSummary s plan response
      · erw [if_neg admitted]; intro response; exact response.elim
  case tool call remaining =>
    by_cases admitted : (authorized s.config s.grant call && artifactAuthorized s call && decide (0 < s.toolDispatches) && decide (s.toolDispatches ≤ s.config.maxToolCalls)) = true
    · erw [if_pos admitted]; intro response
      exact queue_consumeTool s call remaining (by simpa [QueueBound, hp] using bounded) (response.map (app.render call.operation))
    · erw [if_neg admitted]; intro response; exact response.elim

theorem reachable_queue {id : String} {config : Config} {task : String} {s : (State app)}
    (reachable : Reachable id config task s) : QueueBound s := by
  induction reachable with
  | initial => trivial
  | next _ response previous => exact queue_preserved _ previous response

/-- Proof-only phase credit. No runtime fuel or extra serialized state is needed.
An unanswered approval includes the credit for either possible permission result. -/
def phaseCredit (s : (State app)) : Nat :=
  match s.phase with
  | .stopped _ => 0
  | .controlModel => 1
  | .model | .summary => 4 * s.config.maxBatchCalls + 3
  | .waiting _ => 2
  | .controlTools [] => 2
  | .controlTools (call :: remaining) =>
    4 * remaining.length +
      if authorized s.config s.grant call && artifactAuthorized s call then 4 else 6
  | .ask call remaining =>
    4 * remaining.length +
      if authorized s.config (some call) call && artifactAuthorized s call then 5 else 7
  | .tool _ remaining => 4 * remaining.length + 3

def executionRank (s : (State app)) : Nat :=
  (s.config.maxModelAttempts - s.modelAttempts) * (4 * s.config.maxBatchCalls + 3) + phaseCredit s

@[simp] theorem credit_advance (s : (State app)) : phaseCredit (advance s) = phaseCredit s := rfl
@[simp] theorem rank_advance (s : (State app)) : executionRank (advance s) = executionRank s := rfl

theorem queue_credit_bound (s : (State app)) (calls : List (Call app)) (phase : s.phase = .controlTools calls) :
    phaseCredit s ≤ 4 * calls.length + 2 := by
  cases calls with
  | nil => simp [phaseCredit, phase]
  | cons call remaining =>
    simp only [phaseCredit, phase, List.length_cons]
    split <;> omega

private theorem model_ledger (s : (State app)) (observation : ModelObservation) :
    (consumeModel s observation).modelAttempts = s.modelAttempts := by
  cases observation with
  | interrupted => rfl
  | uncertain message => simp only [consumeModel]; unfold retryOrStop; split <;> rfl
  | failure kind message =>
    cases kind <;> simp only [consumeModel]
    all_goals first | rfl | (solve | simp only [repair_modelAttempts]) | (unfold retryOrStop; split <;> rfl)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeModel, hs, hu, accountUsage]
    all_goals repeat' first | rfl | (solve | simp only [repair_modelAttempts]) | split

private theorem summary_ledger (s : (State app)) (plan : SummaryPlan) (observation : ModelObservation) :
    (consumeSummary s plan observation).modelAttempts = s.modelAttempts := by
  cases observation with
  | interrupted => rfl
  | uncertain message => simp only [consumeSummary]; unfold retryOrStop; split <;> rfl
  | failure kind message =>
    cases kind <;> simp only [consumeSummary]
    all_goals first | rfl | (unfold retryOrStop; split <;> rfl)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeSummary, hs, hu, accountUsage]
    all_goals repeat' first | rfl | split | (unfold installSummary; dsimp only)

private theorem tool_ledger (s : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ToolObservation ToolResult) :
    (consumeTool s call remaining observation).modelAttempts = s.modelAttempts := by
  cases observation <;> simp only [consumeTool, retainPartialArtifacts]
  all_goals repeat' first | rfl | split

private theorem repair_reply_credit (s : (State app)) (kind : ResponseRepairKind) (message : String) :
    phaseCredit (repairTaskResponse s kind message) ≤ 4 * s.config.maxBatchCalls + 2 := by
  unfold repairTaskResponse; split <;> simp [phaseCredit, stop]

private theorem model_reply_credit (s : (State app)) (observation : ModelObservation) :
    phaseCredit (consumeModel s observation) ≤ 4 * s.config.maxBatchCalls + 2 := by
  cases observation with
  | interrupted => simp [consumeModel, phaseCredit, stop]
  | uncertain message =>
    simp only [consumeModel]
    unfold retryOrStop
    split <;> simp [phaseCredit, stop]
  | failure kind message =>
    cases kind <;> simp only [consumeModel]
    all_goals first | (solve | simp [phaseCredit, stop]) | (exact repair_reply_credit _ _ _) |
      (unfold retryOrStop; split <;> simp [phaseCredit, stop])
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeModel, hs, hu, accountUsage]
    all_goals repeat' first | (solve | simp [phaseCredit, stop]) | (exact repair_reply_credit _ _ _) | split
    all_goals
      rename_i calls accepted
      have length := (validated_batch_length _ _ _ _ accepted).2
      exact (queue_credit_bound _ calls rfl).trans (by omega)

private theorem summary_reply_credit (s : (State app)) (plan : SummaryPlan) (observation : ModelObservation) :
    phaseCredit (consumeSummary s plan observation) ≤ 2 := by
  cases observation with
  | interrupted => simp [consumeSummary, phaseCredit, stop]
  | uncertain message => simp only [consumeSummary]; unfold retryOrStop; split <;> simp [phaseCredit, stop]
  | failure kind message =>
    cases kind <;> simp only [consumeSummary]
    all_goals first | (solve | simp [phaseCredit, stop]) |
      (unfold retryOrStop; split <;> simp [phaseCredit, stop])
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeSummary, hs, hu, accountUsage]
    all_goals repeat' first
      | (solve | simp [phaseCredit, stop, summaryCandidate])
      | split
      | (unfold installSummary; dsimp only)

private theorem tool_reply_credit (s : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ToolObservation ToolResult) :
    phaseCredit (consumeTool s call remaining observation) ≤ 4 * remaining.length + 2 := by
  cases observation <;> simp only [consumeTool, retainPartialArtifacts]
  all_goals repeat' first
    | (solve | simp [phaseCredit, stop, settleTimedOut])
    | (exact queue_credit_bound _ remaining rfl)
    | split

private theorem rank_same_reservation (before after : (State app))
    (config : after.config = before.config) (attempts : after.modelAttempts = before.modelAttempts)
    (credit : phaseCredit after < phaseCredit before) : executionRank after < executionRank before := by
  simp only [executionRank, config, attempts]
  omega

private theorem next_attempt_rank (maximum attempts credit : Nat) (admitted : attempts < maximum) :
    (maximum - (attempts + 1)) * credit + credit < (maximum - attempts) * credit + 1 := by
  have remainder : maximum - attempts = maximum - (attempts + 1) + 1 := by omega
  rw [remainder, Nat.add_mul]
  omega

private theorem stop_rank (s : (State app)) (outcome : Outcome) (positive : 0 < phaseCredit s) :
    executionRank (stop s outcome) < executionRank s := by
  change (s.config.maxModelAttempts - s.modelAttempts) * (4 * s.config.maxBatchCalls + 3) + 0 <
    (s.config.maxModelAttempts - s.modelAttempts) * (4 * s.config.maxBatchCalls + 3) + phaseCredit s
  omega

private theorem admitTask_rank (s : (State app)) (phase : s.phase = .controlModel) :
    executionRank (admitTask s) < executionRank s := by
  unfold admitTask
  dsimp only
  split
  · rename_i admitted
    split
    · split
      · simpa [executionRank, phaseCredit, phase] using
          next_attempt_rank s.config.maxModelAttempts s.modelAttempts (4 * s.config.maxBatchCalls + 3) admitted
      · exact stop_rank s _ (by simp [phaseCredit, phase])
    · exact stop_rank s _ (by simp [phaseCredit, phase])
  · exact stop_rank s _ (by simp [phaseCredit, phase])

private theorem admitSummary_rank (s : (State app)) (plan : SummaryPlan) (phase : s.phase = .controlModel) :
    executionRank (admitSummary s plan) < executionRank s := by
  unfold admitSummary
  split
  · rename_i admitted
    split
    · simpa [executionRank, phaseCredit, phase] using
        next_attempt_rank s.config.maxModelAttempts s.modelAttempts (4 * s.config.maxBatchCalls + 3) admitted
    · exact stop_rank s _ (by simp [phaseCredit, phase])
  · exact stop_rank s _ (by simp [phaseCredit, phase])

private theorem admitModel_rank (s : (State app)) (phase : s.phase = .controlModel) :
    executionRank (admitModel s) < executionRank s := by
  unfold admitModel
  split
  · exact admitSummary_rank s _ phase
  · split
    · split
      · exact admitSummary_rank s _ phase
      · exact admitTask_rank s phase
    · exact admitTask_rank s phase

private theorem approved_ready (s : (State app)) (call : (Call app)) (permission : policy s.config call = .ask) (artifact : artifactAuthorized s call = true) :
    (authorized s.config (some call) call && artifactAuthorized s call) = true := by
  simp [authorized, permission, artifact]

private theorem admitTool_rank (s : (State app)) (call : (Call app)) (remaining : List (Call app))
    (phase : s.phase = .controlTools (call :: remaining)) :
    executionRank (admitTool s call remaining) < executionRank s := by
  unfold admitTool
  split
  · split
    · rename_i capacity ready
      refine rank_same_reservation s _ ?_ ?_ ?_ <;> try rfl
      simp [phaseCredit, phase, ready]
    · rename_i capacity unready
      split
      · rename_i asks
        have asksBoth : (policy s.config call == .ask) = true ∧ artifactAuthorized s call = true := by
          simpa only [Bool.and_eq_true] using asks
        have permission : policy s.config call = .ask := by
          cases chosen : policy s.config call with
          | ask => rfl
          | allow => simp only [chosen] at asksBoth; cases asksBoth.1
          | deny => simp only [chosen] at asksBoth; cases asksBoth.1
        have artifact := asksBoth.2
        have granted := approved_ready s call permission artifact
        refine rank_same_reservation s _ ?_ ?_ ?_ <;> try rfl
        have priorCredit : phaseCredit s = 4 * remaining.length + 6 := by
          simp [phaseCredit, phase, unready]
        change (4 * remaining.length + if authorized s.config (some call) call && artifactAuthorized s call then 5 else 7) < phaseCredit s
        rw [priorCredit, if_pos granted]
        omega
      · refine rank_same_reservation s _ ?_ ?_ ?_ <;> try rfl
        have credit := queue_credit_bound
          ({appendResult s call "not executed: policy denied" true with phase := .controlTools remaining}) remaining rfl
        have priorCredit : phaseCredit s = 4 * remaining.length + 6 := by
          simp [phaseCredit, phase, unready]
        rw [priorCredit]
        omega
  · refine rank_same_reservation s _ ?_ ?_ ?_ <;> try rfl
    simp only [phaseCredit, stop, phase]
    split <;> omega

private theorem model_rank (s : (State app)) (observation : ModelObservation) (phase : s.phase = .model) :
    executionRank (consumeModel s observation) < executionRank s := by
  apply rank_same_reservation s _ (config_consumeModel s observation) (model_ledger s observation)
  have credit := model_reply_credit s observation
  rw [show phaseCredit s = 4 * s.config.maxBatchCalls + 3 by simp [phaseCredit, phase]]
  omega

private theorem summary_rank (s : (State app)) (plan : SummaryPlan) (observation : ModelObservation)
    (phase : s.phase = .summary) :
    executionRank (consumeSummary s plan observation) < executionRank s := by
  apply rank_same_reservation s _ (config_consumeSummary s plan observation) (summary_ledger s plan observation)
  have credit := summary_reply_credit s plan observation
  rw [show phaseCredit s = 4 * s.config.maxBatchCalls + 3 by simp [phaseCredit, phase]]
  omega

private theorem tool_rank (s : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ToolObservation ToolResult) (phase : s.phase = .tool call remaining) :
    executionRank (consumeTool s call remaining observation) < executionRank s := by
  apply rank_same_reservation s _ (config_consumeTool s call remaining observation)
    (tool_ledger s call remaining observation)
  have credit := tool_reply_credit s call remaining observation
  rw [show phaseCredit s = 4 * remaining.length + 3 by simp [phaseCredit, phase]]
  omega

private theorem approval_rank (s : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ApprovalObservation) (phase : s.phase = .ask call remaining) :
    executionRank (consumeApproval s call remaining observation) < executionRank s := by
  cases observation with
  | approved =>
    refine rank_same_reservation s _ ?_ ?_ ?_ <;> try rfl
    rw [show phaseCredit s = 4 * remaining.length +
      (if authorized s.config (some call) call && artifactAuthorized s call then 5 else 7) by simp [phaseCredit, phase]]
    change (4 * remaining.length + if authorized s.config (some call) call && artifactAuthorized s call then 4 else 6) < _
    split <;> omega
  | denied =>
    refine rank_same_reservation s _ ?_ ?_ ?_ <;> try rfl
    have credit := queue_credit_bound (consumeApproval s call remaining .denied) remaining rfl
    have lower : 4 * remaining.length + 5 ≤ phaseCredit s := by
      simp only [phaseCredit, phase]
      split <;> omega
    omega
  | interrupted =>
    refine rank_same_reservation s _ ?_ ?_ ?_ <;> try rfl
    simp only [consumeApproval, cancelCalls, phaseCredit, phase]
    split <;> omega

private theorem control_model_rank (s : (State app)) (observation : ControlObservation)
    (phase : s.phase = .controlModel) :
    executionRank (consumeControl s none observation) < executionRank s := by
  simp only [consumeControl]
  split
  · exact stop_rank s _ (by simp [phaseCredit, phase])
  · split
    · exact stop_rank s _ (by simp [phaseCredit, phase])
    · exact admitModel_rank s phase

private theorem control_tools_rank (s : (State app)) (calls : List (Call app)) (observation : ControlObservation)
    (phase : s.phase = .controlTools calls) :
    executionRank (consumeControl s (some calls) observation) < executionRank s := by
  have positive : 0 < phaseCredit s := by
    cases calls with
    | nil => simp [phaseCredit, phase]
    | cons call remaining => simp only [phaseCredit, phase]; split <;> omega
  simp only [consumeControl]
  split
  · exact stop_rank s .cancelled positive
  · split
    · exact stop_rank s _ positive
    · cases calls with
      | nil =>
        refine rank_same_reservation s _ ?_ ?_ ?_ <;> simp [phaseCredit, phase]
      | cons call remaining => exact admitTool_rank s call remaining phase

private def ProgressNode (s : (State app)) (node : (HarnessF app) (State app)) : Prop :=
  ∀ response : Reply node.1, executionRank (node.2 response) < executionRank s

/-- Every ordinary consumed reply strictly decreases a finite rank. Administrative
recovery and process scheduling are deliberately outside this relation. -/
theorem execution_rank_decreases (s : (State app)) :
    ∀ response : Reply (step s).1, executionRank ((step s).2 response) < executionRank s := by
  change ProgressNode s (step s)
  cases phase : s.phase <;> simp only [step, phase]
  case stopped outcome => intro response; exact response.elim
  case controlModel => exact fun response => control_model_rank s response phase
  case controlTools calls => exact fun response => control_tools_rank s calls response phase
  case ask call remaining => exact fun response => approval_rank s call remaining response phase
  case waiting delay =>
    intro response
    cases response <;> (refine rank_same_reservation s _ ?_ ?_ ?_ <;>
      simp [phaseCredit, phase, consumeWait, stop, advance])
  case model =>
    by_cases admitted : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts)) = true
    · erw [if_pos admitted]; exact fun response => model_rank s response phase
    · erw [if_neg admitted]; intro response; exact response.elim
  case summary =>
    cases pending : s.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases admitted : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts) && planValid s plan) = true
      · erw [if_pos admitted]; exact fun response => summary_rank s plan response phase
      · erw [if_neg admitted]; intro response; exact response.elim
  case tool call remaining =>
    by_cases admitted : (authorized s.config s.grant call && artifactAuthorized s call && decide (0 < s.toolDispatches) && decide (s.toolDispatches ≤ s.config.maxToolCalls)) = true
    · erw [if_pos admitted]; exact fun response => tool_rank s call remaining (response.map (app.render call.operation)) phase
    · erw [if_neg admitted]; intro response; exact response.elim

theorem execution_trace_bound {first last : (State app)} {events : List (ObservedStep app)}
    (trace : ExecutionTrace first events last) :
    events.length + executionRank last ≤ executionRank first :=
  trace.rank_bound executionRank execution_rank_decreases

/-- Finite ordinary execution bound for the configured single turn. The runner must
still be scheduled, and each external action must return or be interrupted. This
says nothing about task success, wall-clock time, crashes or administrative loops. -/
theorem initialized_reply_bound (id : String) (config : Config) (task : String)
    {last : (State app)} {events : List (ObservedStep app)}
    (trace : ExecutionTrace (init id config task app) events last) :
    events.length ≤ 1 + config.maxModelAttempts * (4 * config.maxBatchCalls + 3) := by
  have bound := execution_trace_bound trace
  simp only [executionRank, phaseCredit, init, Nat.sub_zero] at bound
  omega

/-- A schedule that keeps returning typed replies cannot form an infinite
ordinary execution. Fairness/physical interruption are runner obligations. -/
theorem no_infinite_replies (states : Nat → (State app))
    (responses : (n : Nat) → Reply (step (states n)).1)
    (successor : ∀ n, states (n + 1) = (step (states n)).2 (responses n)) : False :=
  PFunctor.Coalgebra.no_infinite_replies (c := step) executionRank execution_rank_decreases
    states responses successor

/-- Rank exhaustion has an actual finish action, not a stuck nonterminal state.
Every other effect has at least one typed interruption/failure reply. -/
theorem exhausted_rank_finishes (state : (State app)) (exhausted : executionRank state = 0) :
    ∃ outcome, (step state).1 = .finish outcome := by
  cases node : step state with
  | mk action continuation =>
    have decreasing : ∀ response : Reply action, executionRank (continuation response) < 0 := by
      intro response
      have result : ProgressNode state (step state) := execution_rank_decreases state
      rw [node] at result
      have less := result response
      simpa only [exhausted] using less
    cases action with
    | finish outcome => exact ⟨outcome, rfl⟩
    | control => have impossible := decreasing ({} : ControlObservation); omega
    | model request => have impossible := decreasing .interrupted; omega
    | tool call => have impossible := decreasing (.failure "logical progress witness"); omega
    | ask call => have impossible := decreasing .interrupted; omega
    | wait delay => have impossible := decreasing .interrupted; omega

end Harness
