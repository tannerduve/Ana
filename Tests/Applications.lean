import Harness.Applications.Inventory
import Harness.Proofs.Administrative
import Harness.Proofs.RawPrefix
import Harness.Proofs.Progress
import Harness.Proofs.MixedApprovals

/-! Compile-time regression fixtures for the application parameter. These use the
same executable coalgebra and proved invariants for an arbitrary application and
for Inventory's genuinely dependent results; no application invariant is assumed. -/
namespace Tests.Applications
open Harness

example (app : Application) (id : String) (config : Config) (task : String)
    (state : State app) (reachable : Reachable id config task state) :
    CoreValid config state ∧ RawHistoryValid state :=
  ⟨reachable_core_valid reachable, reachable_raw_prefix reachable⟩

example (app : Application) (state : State app) (reply : Reply (step state).1) :
    executionRank ((step state).2 reply) < executionRank state :=
  execution_rank_decreases state reply

example (app : Application) (id : String) (config : Config) (task : String)
    (records : List Lean.Json) (cursor : Recovery.Cursor app)
    (accepted : Recovery.replay (init id config task app) records = .ok cursor) :
    Recovery.CursorCoreValid config cursor ∧ Recovery.CursorProperty RawHistoryValid cursor :=
  ⟨Recovery.replay_core_valid id config task records cursor accepted,
    replay_raw_prefix id config task records cursor accepted⟩

example (state : State Inventory.application) (call : Call Inventory.application)
    (emitted : (step state).1 = .tool call) :
    authorized state.config state.grant call = true :=
  emitted_tool_authorized state call emitted

private def lookup : Call Inventory.application := ⟨"lookup-1", .lookup "A"⟩

example (result : Option Inventory.Item) : Reply (.tool lookup : Action Inventory.application) :=
  .success result

example : True := by
  fail_if_success
    have wrongResult : Reply (.tool lookup : Action Inventory.application) :=
      .success (#[] : Array Inventory.WarehouseSummary)
  trivial

end Tests.Applications
