import Std
def total : List Nat → Nat
  | [] => 0
  | x :: xs => x + total xs
