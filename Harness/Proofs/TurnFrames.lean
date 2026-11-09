import Harness.Core.Recovery
import Harness.Proofs.Except

/-! Exact admission and ledger frames for trusted user turns. These facts concern
the executable checks and updates, not authentication of the caller or fsync. -/
namespace Harness
open Lean ExceptRules
variable {app : Application}

theorem begin_turn_contract (before after : State app) (task : String)
    (accepted : beginTurn before task = .ok after) :
    after = turnCandidate before task ∧ acceptsNewTurn before = true ∧
      historyValid before.history = true ∧ historyValid (activeMessages after) = true := by
  simp only [beginTurn, pure_ok, throw_error, error_bind] at accepted
  split at accepted
  · rename_i ready
    split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · split at accepted
        · split at accepted
          · rename_i closed
            split at accepted
            · rename_i paired
              cases accepted
              exact ⟨rfl, ready, closed, paired⟩
            · cases accepted
          · cases accepted
        · cases accepted
  · cases accepted

theorem begin_turn_preserves_authority_and_accounting (before after : State app) (task : String)
    (accepted : beginTurn before task = .ok after) :
    after.config = before.config ∧ after.sessionId = before.sessionId ∧
    after.modelAttempts = before.modelAttempts ∧ after.toolDispatches = before.toolDispatches ∧
    after.knownInputTokens = before.knownInputTokens ∧ after.knownOutputTokens = before.knownOutputTokens ∧
    after.unknownUsage = before.unknownUsage ∧ after.responseRepairs = before.responseRepairs ∧
    after.seenCallIds = before.seenCallIds ∧ after.artifacts = before.artifacts ∧
    after.activeView = before.activeView ∧ after.summaries = before.summaries ∧
    after.grant = none ∧ after.pendingSummary = none ∧ after.phase = .controlModel ∧
    after.nextId = before.nextId + 1 ∧ after.turn = before.turn + 1 := by
  rw [(begin_turn_contract before after task accepted).1]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace Recovery

theorem new_turn_contract (before after : Cursor app) (id turn : Nat) (task : String)
    (accepted : newTurn before id turn task = .ok after) :
    before.terminal = true ∧ before.pending = false ∧ before.suspended = none ∧ before.editWitness = none ∧
    id = before.state.nextId ∧ turn = before.state.turn + 1 ∧
    beginTurn before.state task = .ok after.state ∧
    after.pending = false ∧ after.terminal = false ∧ after.suspended = none ∧ after.editWitness = none := by
  by_cases terminal : before.terminal = true
  · by_cases invalid : (before.pending || before.suspended.isSome || before.editWitness.isSome) = true
    · simp [newTurn, terminal, invalid] at accepted
    · by_cases same : (id == before.state.nextId && turn == before.state.turn + 1) = true
      · cases started : beginTurn before.state task with
        | error message => simp [newTurn, terminal, invalid, same, started] at accepted
        | ok state =>
          simp only [newTurn, terminal, invalid, same,
            Bool.false_eq_true, ↓reduceIte, started, ok_bind, pure_ok, Except.ok.injEq] at accepted
          subst after
          have clear : before.pending = false ∧ before.suspended = none ∧ before.editWitness = none := by
            simpa only [Bool.or_eq_true, not_or, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, and_assoc] using invalid
          have ids : id = before.state.nextId ∧ turn = before.state.turn + 1 := by
            simpa only [Bool.and_eq_true, beq_iff_eq] using same
          exact ⟨terminal, clear.1, clear.2.1, clear.2.2, ids.1, ids.2, rfl, rfl, rfl, rfl, rfl⟩
      · simp [newTurn, terminal, invalid, same] at accepted
  · simp [newTurn, terminal] at accepted

theorem user_turn_record_replays (cursor : Cursor app) (id turn : Nat) (task : String) :
    applyRecord cursor (userTurnRecord id turn task) = newTurn cursor id turn task := by
  rfl

end Recovery
end Harness
