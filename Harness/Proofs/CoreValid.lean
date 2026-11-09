import Harness.Proofs.ResponseRepairBudget
import Harness.Proofs.Transcript
import Harness.Proofs.Artifacts

namespace Harness

variable {app : Application}

/-- Joint logical invariant used by ordinary execution and administrative
recovery. IO containment, trusted approval delivery, durable storage and summary
fidelity are deliberately not asserted by this predicate. -/
structure CoreValid (config : Config) (state : (State app)) : Prop where
  frozen : state.config = config
  budgets : BudgetValid state
  calls : CallsValid state
  results : ResultsValid state
  taskHistory : TaskHistoryValid state
  artifacts : ArtifactsValid state
  repairs : ResponseRepairValid state

theorem core_valid_init (id : String) (config : Config) (task : String) :
    CoreValid config (init id config task app) := by
  exact ⟨rfl, budget_init _ _ _, reachable_calls .initial,
    reachable_result_correlation .initial, reachable_task_history .initial, artifacts_init _ _ _, reachable_response_repairs .initial⟩

theorem core_valid_step (config : Config) (state : (State app)) (valid : CoreValid config state)
    (response : Reply (step state).1) : CoreValid config ((step state).2 response) := by
  exact ⟨(config_preserved state response).trans valid.frozen,
    budget_preserved state valid.budgets response,
    calls_preserved state valid.calls response,
    result_history_preserved state valid.calls valid.results response,
    task_history_preserved state response,
    (artifact_registry_preserved state valid.artifacts response).2,
    response_repair_valid_step state valid.repairs response⟩

theorem reachable_core_valid {id : String} {config : Config} {task : String} {state : (State app)}
    (reachable : Reachable id config task state) : CoreValid config state :=
  reachable.invariant (core_valid_init _ _ _) (core_valid_step config)

end Harness
