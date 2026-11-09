import Harness.Proofs.Invariants
import Harness.Proofs.Trace

/-! Operation identity is a session ledger: every consumed ordinary reply advances
its serial number exactly once and preserves the trusted user-turn index. This
is independent of the application and of the contents of a typed observation. -/
namespace Harness

variable {app : Application}

def State.operationIdentity (s : State app) : Nat × Nat := (s.nextId, s.turn)

private theorem identity_after_advance {before after : State app}
    (same : after.operationIdentity = before.operationIdentity) :
    (advance after).operationIdentity = (before.nextId + 1, before.turn) :=
  congrArg (fun key : Nat × Nat => (key.1 + 1, key.2)) same

private theorem identity_repair (s : State app) (kind : ResponseRepairKind) (message : String) :
    (repairTaskResponse s kind message).operationIdentity = s.operationIdentity := by
  unfold repairTaskResponse
  split <;> rfl

private theorem identity_consumeModel (s : (State app)) (observation : ModelObservation) :
    (consumeModel s observation).operationIdentity = s.operationIdentity := by
  cases observation with
  | interrupted => rfl
  | uncertain message => simp only [consumeModel]; unfold retryOrStop; split <;> rfl
  | failure kind message =>
    cases kind <;> simp only [consumeModel]
    all_goals first | rfl | (solve | rw [identity_repair]; rfl) | (unfold retryOrStop; split <;> rfl)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeModel, hs, hu, accountUsage]
    all_goals repeat' first | rfl | (solve | rw [identity_repair]; rfl) | split

private theorem identity_admitModel (s : (State app)) : (admitModel s).operationIdentity = s.operationIdentity := by
  unfold admitModel
  repeat' first | rfl | split | (unfold admitTask; dsimp only) | (unfold admitSummary)

private theorem identity_consumeSummary (s : (State app)) (plan : SummaryPlan) (observation : ModelObservation) :
    (consumeSummary s plan observation).operationIdentity = s.operationIdentity := by
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

private theorem identity_admitTool (s : (State app)) (call : (Call app)) (rest : List (Call app)) :
    (admitTool s call rest).operationIdentity = s.operationIdentity := by
  unfold admitTool
  repeat' first | rfl | split

private theorem identity_consumeControl (s : (State app)) (calls : Option (List (Call app)))
    (observation : ControlObservation) :
    (consumeControl s calls observation).operationIdentity = s.operationIdentity := by
  cases calls with
  | none =>
    simp only [consumeControl]
    split
    · rfl
    · split
      · rfl
      · exact identity_admitModel s
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
        · exact identity_admitTool s call rest

private theorem identity_consumeTool (s : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ToolObservation ToolResult) :
    (consumeTool s call remaining observation).operationIdentity = s.operationIdentity := by
  cases observation <;> simp only [consumeTool, retainPartialArtifacts]
  all_goals repeat' first | rfl | split

private theorem identity_consumeApproval (s : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ApprovalObservation) :
    (consumeApproval s call remaining observation).operationIdentity = s.operationIdentity := by
  cases observation <;> rfl

private theorem identity_consumeWait (s : (State app)) (observation : WaitObservation) :
    (consumeWait s observation).operationIdentity = s.operationIdentity := by
  cases observation <;> rfl

private def IdentityNode (key : Nat × Nat) (node : (HarnessF app) (State app)) : Prop :=
  ∀ response : Reply node.fst, (node.snd response).operationIdentity = (key.1 + 1, key.2)

/-- Exact operation/turn ledger update by the executable coalgebra. -/
private theorem identity_preserved (s : (State app)) :
    ∀ response : Reply (step s).fst, ((step s).snd response).operationIdentity = (s.nextId + 1, s.turn) := by
  change IdentityNode s.operationIdentity (step s)
  cases hp : s.phase <;> simp only [step, hp]
  case stopped outcome => intro response; exact response.elim
  case controlModel => exact fun response => identity_after_advance (identity_consumeControl _ none response)
  case controlTools calls => exact fun response => identity_after_advance (identity_consumeControl _ (some calls) response)
  case ask call rest => exact fun response => identity_after_advance (identity_consumeApproval _ call rest response)
  case waiting delay => exact fun response => identity_after_advance (identity_consumeWait _ response)
  case model =>
    by_cases permitted : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts)) = true
    · erw [if_pos permitted]; exact fun response => identity_after_advance (identity_consumeModel _ response)
    · erw [if_neg permitted]; intro response; exact response.elim
  case summary =>
    cases hpending : s.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases permitted : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts) && planValid s plan) = true
      · erw [if_pos permitted]; exact fun response => identity_after_advance (identity_consumeSummary _ plan response)
      · erw [if_neg permitted]; intro response; exact response.elim
  case tool call rest =>
    by_cases permitted : (authorized s.config s.grant call && artifactAuthorized s call && decide (0 < s.toolDispatches) && decide (s.toolDispatches ≤ s.config.maxToolCalls)) = true
    · erw [if_pos permitted]; exact fun response => identity_after_advance (identity_consumeTool _ call rest (response.map (app.render call.operation)))
    · erw [if_neg permitted]; intro response; exact response.elim


theorem step_advances_operation_id (state : State app) (response : Reply (step state).1) :
    ((step state).2 response).nextId = state.nextId + 1 :=
  congrArg Prod.fst (identity_preserved state response)

theorem step_preserves_turn (state : State app) (response : Reply (step state).1) :
    ((step state).2 response).turn = state.turn :=
  congrArg Prod.snd (identity_preserved state response)

theorem ExecutionTrace.operation_ids {first last : State app} {events : List (ObservedStep app)}
    (trace : ExecutionTrace first events last) :
    events.map (·.operation) = List.range' first.nextId events.length := by
  induction trace with
  | nil => rfl
  | cons state response tail ih =>
    simp only [List.map_cons, observe, List.length_cons, List.range'_succ, ih,
      step_advances_operation_id]

theorem ExecutionTrace.operation_ids_unique {first last : State app} {events : List (ObservedStep app)}
    (trace : ExecutionTrace first events last) : (events.map (·.operation)).Nodup := by
  rw [trace.operation_ids]
  exact List.nodup_range'

end Harness
