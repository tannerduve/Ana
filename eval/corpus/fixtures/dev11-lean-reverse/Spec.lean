import Proof
example (xs : List Nat) : xs.reverse.reverse = xs := reverse_twice xs
#print axioms reverse_twice
