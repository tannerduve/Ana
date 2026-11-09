import Harness.Proofs.Configuration
import Harness.Proofs.Trace

/-! The separate repair allowance is real durable policy state. Ordinary replies
never restore it, and every admitted repair stays below the frozen ceiling. Model
attempts and summary/transport retry accounting retain their existing proofs. -/
namespace Harness

variable {app : Application}

def ResponseRepairValid (state : (State app)) : Prop :=
  state.responseRepairs ≤ state.config.maxResponseRepairs

def RepairCountUpdate (before after : (State app)) : Prop :=
  before.responseRepairs ≤ after.responseRepairs ∧
  after.responseRepairs ≤ before.config.maxResponseRepairs

@[simp] theorem repair_count_advance (state : (State app)) :
    (advance state).responseRepairs = state.responseRepairs := rfl

private theorem model_repairs (state : (State app)) (observation : ModelObservation)
    (bounded : ResponseRepairValid state) : RepairCountUpdate state (consumeModel state observation) := by
  cases observation with
  | interrupted => exact ⟨Nat.le_refl _, bounded⟩
  | uncertain message =>
    simp only [consumeModel]; unfold retryOrStop; split <;> exact ⟨Nat.le_refl _,bounded⟩
  | failure kind message =>
    cases kind <;> simp only [consumeModel]
    all_goals first
      | exact ⟨Nat.le_refl _,bounded⟩
      | (unfold repairTaskResponse; split <;> simp_all [RepairCountUpdate, ResponseRepairValid, stop]; omega)
      | (unfold retryOrStop; split <;> exact ⟨Nat.le_refl _,bounded⟩)
  | success response =>
    cases usage : response.usage <;> cases reason : response.stop <;>
      simp only [consumeModel, reason, usage, accountUsage]
    all_goals repeat' first
      | exact ⟨Nat.le_refl _,bounded⟩
      | (unfold repairTaskResponse; split <;> simp_all [RepairCountUpdate, ResponseRepairValid, stop]; omega)
      | split

theorem summary_responseRepairs (state : (State app)) (plan : SummaryPlan) (observation : ModelObservation) :
    (consumeSummary state plan observation).responseRepairs = state.responseRepairs := by
  cases observation with
  | interrupted => rfl
  | uncertain message => simp only [consumeSummary]; unfold retryOrStop; split <;> rfl
  | failure kind message =>
    cases kind <;> simp only [consumeSummary]
    all_goals first | rfl | (unfold retryOrStop; split <;> rfl)
  | success response =>
    cases usage : response.usage <;> cases reason : response.stop <;>
      simp only [consumeSummary, reason, usage, accountUsage]
    all_goals repeat' first | rfl | split | (unfold installSummary; dsimp only)

theorem tool_responseRepairs (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ToolObservation ToolResult) :
    (consumeTool state call remaining observation).responseRepairs = state.responseRepairs := by
  cases observation <;> simp only [consumeTool, retainPartialArtifacts]
  all_goals repeat' first | rfl | split

private theorem control_responseRepairs (state : (State app)) (calls : Option (List (Call app)))
    (observation : ControlObservation) :
    (consumeControl state calls observation).responseRepairs = state.responseRepairs := by
  unfold consumeControl
  repeat' first | rfl | split | unfold admitModel | (unfold admitTask; dsimp only) | unfold admitSummary | unfold admitTool

private def RepairNode (state : (State app)) (node : (HarnessF app) (State app)) : Prop :=
  ∀ response : Reply node.1, RepairCountUpdate state (node.2 response)

/-- Every actual reply preserves the separate ceiling and cannot decrease its
consumed repair count. The premise is just the previous numeric bound. -/
theorem response_repair_count_step (state : (State app)) (bounded : ResponseRepairValid state) :
    ∀ response : Reply (step state).1, RepairCountUpdate state ((step state).2 response) := by
  change RepairNode state (step state)
  cases phase : state.phase <;> simp only [step, phase]
  case stopped outcome => intro response; exact response.elim
  case controlModel =>
    intro response
    simp only [RepairCountUpdate, repair_count_advance, control_responseRepairs]
    exact ⟨Nat.le_refl _,bounded⟩
  case controlTools calls =>
    intro response
    simp only [RepairCountUpdate, repair_count_advance, control_responseRepairs]
    exact ⟨Nat.le_refl _,bounded⟩
  case ask call remaining => intro response; cases response <;> exact ⟨Nat.le_refl _,bounded⟩
  case waiting delay => intro response; cases response <;> exact ⟨Nat.le_refl _,bounded⟩
  case model =>
    by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts)) = true
    · erw [if_pos admitted]; exact fun response => model_repairs state response bounded
    · erw [if_neg admitted]; intro response; exact response.elim
  case summary =>
    cases pending : state.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts) && planValid state plan) = true
      · erw [if_pos admitted]; intro response
        simp only [RepairCountUpdate, repair_count_advance, summary_responseRepairs]
        exact ⟨Nat.le_refl _,bounded⟩
      · erw [if_neg admitted]; intro response; exact response.elim
  case tool call remaining =>
    by_cases admitted : (authorized state.config state.grant call && artifactAuthorized state call && decide (0 < state.toolDispatches) && decide (state.toolDispatches ≤ state.config.maxToolCalls)) = true
    · erw [if_pos admitted]; intro response
      simp only [RepairCountUpdate, repair_count_advance, tool_responseRepairs]
      exact ⟨Nat.le_refl _,bounded⟩
    · erw [if_neg admitted]; intro response; exact response.elim

theorem response_repair_valid_step (state : (State app)) (bounded : ResponseRepairValid state)
    (response : Reply (step state).1) : ResponseRepairValid ((step state).2 response) := by
  unfold ResponseRepairValid
  rw [config_preserved state response]
  exact (response_repair_count_step state bounded response).2

theorem reachable_response_repairs {id : String} {config : Config} {task : String} {state : (State app)}
    (reachable : Reachable id config task state) : ResponseRepairValid state :=
  reachable.invariant (by simp [ResponseRepairValid, init]) response_repair_valid_step

/-- Along ordinary execution the consumed repair allowance is monotone. -/
theorem ExecutionTrace.responseRepairs_monotone {first last : (State app)} {events : List (ObservedStep app)}
    (trace : ExecutionTrace first events last) (valid : ResponseRepairValid first) :
    first.responseRepairs ≤ last.responseRepairs ∧ ResponseRepairValid last :=
  trace.accumulate (r := fun before after => before.responseRepairs ≤ after.responseRepairs)
    (fun _ => Nat.le_refl _) (fun left right => left.trans right)
    (fun state bounded response => ⟨(response_repair_count_step state bounded response).1,
      response_repair_valid_step state bounded response⟩) valid

end Harness
