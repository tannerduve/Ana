import Definitions
theorem transform_append {α β : Type} (f : α → β) (xs ys : List α) : transform f (xs ++ ys) = transform f xs ++ transform f ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [transform, ih]
