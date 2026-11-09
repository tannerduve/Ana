import Definitions
theorem total_append (xs ys : List Nat) : total (xs ++ ys) = total xs + total ys := by
  rfl
