import Harness.Applications.InventoryData
import Harness.Proofs.Except
import Mathlib.Data.Nat.Basic

/-! Stock arithmetic for the executable pure reservation update. Accepted updates
debit the selected SKU by exactly a positive quantity no greater than its prior
stock and retain every other item. IO durability and unique ledger keys are
separate interpreter obligations. -/
namespace Harness.Inventory
open Lean ExceptRules

/-- The pre-debit stock comes from the input dataset; the result cannot oversell
or alter another SKU. Identity is supplied by the runner's key, not the model. -/
theorem reserve_stock_contract (data : Dataset) (key : ReservationKey) (op : Operation)
    (next : Dataset) (receipt : Reservation)
    (accepted : reserve data key op = .ok (next, receipt)) :
    receipt.sessionId = key.sessionId ∧ receipt.operationId = key.operationId ∧
    op = .reserve receipt.sku receipt.units ∧ 0 < receipt.units ∧
    receipt.units ≤ receipt.before ∧ receipt.remaining + receipt.units = receipt.before ∧
    (∃ item, data.items.find? (fun item => item.sku == receipt.sku) = some item ∧
      receipt.before = item.onHand) ∧
    next.version = data.version ∧
    next.items = data.items.map (fun row =>
      if row.sku == receipt.sku then {row with onHand := receipt.remaining} else row) := by
  cases op <;> simp only [reserve, pure_ok, throw_error, error_bind] at accepted
  all_goals try contradiction
  rename_i sku units
  split at accepted
  · rename_i valid
    obtain ⟨_, _, accepted⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
    cases found : data.items.find? (fun item => item.sku == sku) with
    | none => simp only [found] at accepted; contradiction
    | some item =>
      simp only [found] at accepted
      split at accepted
      · rename_i enough
        cases accepted
        have positive : 0 < units := by
          simp only [Bool.and_eq_true, validReservationArgs, decide_eq_true_eq] at valid
          exact valid.2.1.2
        exact ⟨rfl, rfl, rfl, positive, enough, Nat.sub_add_cancel enough,
          ⟨item, found, rfl⟩, rfl, rfl⟩
      · cases accepted
  · cases accepted

end Harness.Inventory
