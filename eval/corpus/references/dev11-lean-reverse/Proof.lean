import Definitions
theorem reverse_twice (xs : List Nat) : xs.reverse.reverse = xs := by
  simp
