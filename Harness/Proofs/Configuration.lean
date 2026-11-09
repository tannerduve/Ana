import Harness.Proofs.Invariants

namespace Harness

@[simp] theorem config_advance (s : State) : (advance s).config = s.config := rfl

@[simp] theorem config_stop (s : State) (outcome : Outcome) :
    (stop s outcome).config = s.config := rfl

@[simp] theorem config_appendResult (s : State) (call : ToolCall) (text : String) (error : Bool) :
    (appendResult s call text error).config = s.config := rfl

theorem config_consumeModel (s : State) (observation : ModelObservation) :
    (consumeModel s observation).config = s.config := by
  cases observation with
  | interrupted => rfl
  | uncertain message => simp only [consumeModel]; unfold retryOrStop; split <;> rfl
  | failure kind message =>
    cases kind <;> simp only [consumeModel]
    all_goals first | rfl | (unfold retryOrStop; split <;> rfl)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeModel, hs, hu, accountUsage]
    all_goals repeat' first | rfl | split

theorem config_admitModel (s : State) : (admitModel s).config = s.config := by
  unfold admitModel
  repeat' first | rfl | split | (unfold admitTask) | (unfold admitSummary)

theorem config_consumeSummary (s : State) (plan : SummaryPlan) (observation : ModelObservation) :
    (consumeSummary s plan observation).config = s.config := by
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

theorem config_admitTool (s : State) (call : ToolCall) (rest : List ToolCall) :
    (admitTool s call rest).config = s.config := by
  unfold admitTool
  repeat' first | rfl | split

theorem config_consumeControl (s : State) (calls : Option (List ToolCall))
    (observation : ControlObservation) :
    (consumeControl s calls observation).config = s.config := by
  cases calls with
  | none =>
    simp only [consumeControl]
    split
    · rfl
    · split
      · rfl
      · exact config_admitModel s
  | some calls =>
    cases calls with
    | nil =>
      simp only [consumeControl]
      repeat' first | rfl | split
    | cons call rest =>
      simp only [consumeControl]
      split
      · rfl
      · split
        · rfl
        · exact config_admitTool s call rest

theorem config_consumeTool (s : State) (call : ToolCall) (remaining : List ToolCall)
    (observation : ToolObservation ToolResult) :
    (consumeTool s call remaining observation).config = s.config := by
  cases observation <;> rfl

theorem config_consumeApproval (s : State) (call : ToolCall) (remaining : List ToolCall)
    (observation : ApprovalObservation) :
    (consumeApproval s call remaining observation).config = s.config := by
  cases observation <;> rfl

theorem config_consumeWait (s : State) (observation : WaitObservation) :
    (consumeWait s observation).config = s.config := by
  cases observation <;> rfl

private def ConfigurationNode (config : Config) (node : HarnessF State) : Prop :=
  ∀ response : Reply node.fst, (node.snd response).config = config

/-- No typed observation can alter the session configuration through the executable
coalgebra. This includes model/tool output as well as trusted control/approval input. -/
theorem config_preserved (s : State) :
    ∀ response : Reply (step s).fst, ((step s).snd response).config = s.config := by
  change ConfigurationNode s.config (step s)
  cases hp : s.phase <;> simp only [step, hp]
  case stopped outcome => intro response; exact response.elim
  case controlModel => exact fun response => config_consumeControl _ none response
  case controlTools calls => exact fun response => config_consumeControl _ (some calls) response
  case ask call rest => exact fun response => config_consumeApproval _ call rest response
  case waiting delay => exact fun response => config_consumeWait _ response
  case model =>
    by_cases permitted : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts)) = true
    · erw [if_pos permitted]; exact fun response => config_consumeModel _ response
    · erw [if_neg permitted]; intro response; exact response.elim
  case summary =>
    cases hpending : s.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases permitted : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts) && planValid s plan) = true
      · erw [if_pos permitted]; exact fun response => config_consumeSummary _ plan response
      · erw [if_neg permitted]; intro response; exact response.elim
  case tool call rest =>
    by_cases permitted : (authorized s.config s.grant call && decide (0 < s.toolDispatches) && decide (s.toolDispatches ≤ s.config.maxToolCalls)) = true
    · erw [if_pos permitted]; exact fun response => config_consumeTool _ call rest response
    · erw [if_neg permitted]; intro response; exact response.elim

/-- Every state reached from initialization retains the exact initial policy,
workspace, instructions, model identity and resource limits. -/
theorem reachable_config {id : String} {config : Config} {task : String} {s : State}
    (reachable : Reachable id config task s) : s.config = config := by
  induction reachable with
  | initial => rfl
  | next _ response previous => exact (config_preserved _ response).trans previous

end Harness
