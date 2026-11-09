import Harness.Proofs.Turns
import Harness.Proofs.RecoveryInvariant

/-! Specializes the shared recovery-preservation rules to the joint core invariant:
frozen configuration, budgets, call/result correlation, admitted task history and
artifact registry validity. Public theorem statements retain their previous scope.
The suspended state remains tied to its exact uncertain continuation. Actual
journal durability and the truth of operator assertions are outside this proof. -/

namespace Harness.Recovery

variable {app : Application}
open Lean

/-- Shared cursor invariant specialized to the joint executable-core properties. -/
abbrev CursorCoreValid (config : Config) (cursor : (Cursor app)) : Prop :=
  CursorProperty (CoreValid config) cursor

private theorem core_clear_grant (config : Config) (state : (State app)) (valid : CoreValid config state) :
    CoreValid config (advance {state with grant := none}) := by
  exact ⟨valid.frozen, valid.budgets, valid.calls, valid.results, valid.taskHistory, valid.artifacts, valid.repairs⟩

private theorem core_approval_retry (config : Config) (state : (State app)) (valid : CoreValid config state)
    (call : (Call app)) (remaining : List (Call app)) (phase : state.phase = .ask call remaining) :
    CoreValid config (advance {state with phase := .controlTools (call :: remaining), grant := none}) := by
  refine ⟨valid.frozen, valid.budgets, ?_, ?_, by trivial, valid.artifacts, valid.repairs⟩
  · simpa [CallsValid, pendingCalls, advance, phase] using valid.calls
  · simpa [ResultsValid, RetiredCall, pendingCalls, advance, phase] using valid.results

private theorem core_artifact_overlay (config : Config) (old current : (State app))
    (oldValid : CoreValid config old) (currentValid : CoreValid config current)
    (call : (Call app)) (emitted : (step old).1 = .tool call) :
    CoreValid config {old with artifacts := current.artifacts} := by
  refine ⟨oldValid.frozen, oldValid.budgets, oldValid.calls, oldValid.results, ?_, ?_, oldValid.repairs⟩
  · cases phase : old.phase <;> simp [TaskHistoryValid]
    by_cases guard : (decide (0 < old.modelAttempts) && decide (old.modelAttempts ≤ old.config.maxModelAttempts)) = true
    · simp [step, phase, guard] at emitted
    · simp [step, phase, guard] at emitted
  · change ArtifactRegistryValid old.config current.artifacts
    rw [oldValid.frozen, ← currentValid.frozen]
    exact currentValid.artifacts

private theorem coreRecoveryRules (config : Config) : RecoveryRules (CoreValid (app := app) config) where
  step := core_valid_step config
  userTurn := begin_turn_core_valid config
  clearGrant := core_clear_grant config
  approvalRetry := core_approval_retry config
  artifactOverlay := core_artifact_overlay config

theorem checked_target_core_valid (config : Config) (cursor : (Cursor app)) (prior : (State app))
    (valid : CursorCoreValid config cursor) (accepted : checkedTarget cursor = .ok prior) :
    CoreValid config prior := checked_target_property (coreRecoveryRules config) cursor prior valid accepted

theorem complete_core_valid (config : Config) (cursor : (Cursor app))
    (valid : CursorCoreValid config cursor) (response : Reply (step cursor.state).1) :
    CursorCoreValid config (complete cursor response) :=
  complete_property (coreRecoveryRules config) cursor valid response

theorem recover_core_valid (config : Config) (cursor next : (Cursor app)) (id : Nat)
    (disposition : Disposition) (valid : CursorCoreValid config cursor)
    (accepted : recover cursor id disposition = .ok next) : CursorCoreValid config next :=
  recover_property (coreRecoveryRules config) cursor next id disposition valid accepted

theorem resolve_core_valid (config : Config) (cursor next : (Cursor app)) (id : Nat)
    (resolution : app.Resolution) (valid : CursorCoreValid config cursor)
    (accepted : resolve cursor id resolution = .ok next) : CursorCoreValid config next :=
  resolve_property (coreRecoveryRules config) cursor next id resolution valid accepted

theorem apply_record_core_valid (config : Config) (cursor next : (Cursor app)) (record : Json)
    (valid : CursorCoreValid config cursor) (accepted : applyRecord cursor record = .ok next) :
    CursorCoreValid config next :=
  apply_record_property (coreRecoveryRules config) cursor next record valid accepted

theorem replay_core_valid (id : String) (config : Config) (task : String)
    (records : List Json) (next : (Cursor app))
    (accepted : replay (init id config task app) records = .ok next) :
    CursorCoreValid config next :=
  replay_property (coreRecoveryRules config) (init id config task app) (core_valid_init id config task)
    records next accepted

end Harness.Recovery
