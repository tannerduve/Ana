import Proof
example (xs ys : List Nat) : total (xs ++ ys) = total xs + total ys := total_append xs ys
#print axioms total_append
