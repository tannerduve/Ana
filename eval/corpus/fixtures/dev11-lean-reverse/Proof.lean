import Definitions
theorem reverse_twice (xs : List Nat) : xs.reverse.reverse = xs := by
  exact List.reverse_involution_old xs
