import Harness.Proofs.Administrative
import Harness.Proofs.RecoveryLedger

namespace Harness.Recovery

variable {app : Application}

/-- Reopening a suspended position uses current reservations. Equality follows
from the exact uncertain-continuation witness in CursorCoreValid, not merely
from equal ceilings or a caller-supplied checkpoint. -/
theorem checked_target_current_reservations (config : Config) (cursor : (Cursor app)) (prior : (State app))
    (valid : CursorCoreValid config cursor) (accepted : checkedTarget cursor = .ok prior) :
    SameReservations cursor.state prior := by
  by_cases pending : cursor.pending = true
  · by_cases invalid : (cursor.terminal || cursor.suspended.isSome) = true
    · simp [checkedTarget, pending, invalid] at accepted
    · have equal : cursor.state = prior := by simpa [checkedTarget, pending, invalid] using accepted
      cases equal
      exact ⟨rfl, rfl⟩
  · cases saved : cursor.suspended with
    | none => simp [checkedTarget, pending, saved] at accepted
    | some old =>
      obtain ⟨_, response, uncertain, current⟩ := valid.suspended old saved
      have ledger := uncertain_reply_reservations old response uncertain
      rw [← current] at ledger
      simp only [checkedTarget, pending, Bool.false_eq_true, ↓reduceIte, saved] at accepted
      split at accepted
      · cases action : (step old).1 <;> simp only [action] at accepted
        all_goals simp at accepted
        rw [← accepted]
        exact ⟨ledger.1.symm, ledger.2.symm⟩
      · simp at accepted

theorem resolution_preserves_current_reservations (config : Config) (cursor next : (Cursor app)) (id : Nat)
    (resolution : app.Resolution) (valid : CursorCoreValid config cursor)
    (accepted : resolve cursor id resolution = .ok next) : SameReservations cursor.state next.state := by
  cases target : checkedTarget cursor with
  | error message => simp [resolve, target] at accepted
  | ok prior =>
    have current := checked_target_current_reservations config cursor prior valid target
    have settled := resolution_target_reservations cursor next prior id resolution target accepted
    exact ⟨settled.1.trans current.1, settled.2.trans current.2⟩

theorem recovery_preserves_current_reservations (config : Config) (cursor next : (Cursor app)) (id : Nat)
    (disposition : Disposition) (valid : CursorCoreValid config cursor)
    (accepted : recover cursor id disposition = .ok next) : SameReservations cursor.state next.state := by
  cases target : checkedTarget cursor with
  | error message => simp [recover, target] at accepted
  | ok prior =>
    have current := checked_target_current_reservations config cursor prior valid target
    have settled := recovery_target_reservations cursor next prior id disposition target accepted
    exact ⟨settled.1.trans current.1, settled.2.trans current.2⟩

end Harness.Recovery
