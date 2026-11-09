import Proof
example {α β : Type} (f : α → β) (xs ys : List α) : transform f (xs ++ ys) = transform f xs ++ transform f ys := transform_append f xs ys
#print axioms transform_append
