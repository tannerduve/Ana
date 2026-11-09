import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Logic.Relation
import Lean.Elab.Tactic.Omega

/-!
Finite executions of a polynomial coalgebra. A successor follows one of the
reply branches supplied by the coalgebra; event labels only record that choice.
Predicate lifting uses Mathlib's `Functor.Liftp`, and reachability uses its
`Relation.ReflTransGen`. These lemmas have no harness or IO dependencies.
-/

namespace PFunctor.Coalgebra

universe uA uB uS uE

variable {P : PFunctor.{uA, uB}} {S : Type uS} {E : Type uE}

/-- One reply selects one continuation of the emitted request. -/
def Next (c : S → P S) (before after : S) : Prop :=
  ∃ reply : P.B (c before).1, (c before).2 reply = after

/-- A predicate closed under the functor's branches holds at every reachable state. -/
theorem invariant {c : S → P S} {property : S → Prop}
    (closed : ∀ state, property state → Functor.Liftp property (c state))
    {first last : S} (path : Relation.ReflTransGen (Next c) first last)
    (initial : property first) : property last := by
  induction path with
  | refl => exact initial
  | tail prior edge ih =>
    obtain ⟨reply, rfl⟩ := edge
    exact (PFunctor.liftp_iff' property _ _).mp (closed _ ih) reply

/-- Actual coalgebra continuations, annotated by any chosen event encoding. -/
inductive Trace (c : S → P S) (observe : (state : S) → P.B (c state).1 → E) :
    S → List E → S → Prop where
  | nil (state : S) : Trace c observe state [] state
  | cons (state : S) (reply : P.B (c state).1)
      {events : List E} {last : S}
      (tail : Trace c observe ((c state).2 reply) events last) :
      Trace c observe state (observe state reply :: events) last

variable {c : S → P S} {observe : (state : S) → P.B (c state).1 → E}

theorem Trace.append {first middle last : S} {left right : List E}
    (a : Trace c observe first left middle) (b : Trace c observe middle right last) :
    Trace c observe first (left ++ right) last := by
  induction a with
  | nil => exact b
  | cons state reply tail ih => exact .cons state reply (ih b)

theorem Trace.to_reflTransGen {first last : S} {events : List E}
    (trace : Trace c observe first events last) :
    Relation.ReflTransGen (Next c) first last := by
  induction trace with
  | nil => exact .refl
  | cons state reply tail ih => exact ih.head ⟨reply, rfl⟩

theorem Trace.invariant {first last : S} {events : List E}
    (trace : Trace c observe first events last) {property : S → Prop}
    (closed : ∀ state, property state → Functor.Liftp property (c state))
    (initial : property first) : property last :=
  Coalgebra.invariant closed trace.to_reflTransGen initial

/-- Accumulate a reflexive, transitive relation while preserving an invariant. -/
theorem Trace.accumulate {first last : S} {events : List E}
    (trace : Trace c observe first events last) {property : S → Prop} {r : S → S → Prop}
    (refl : ∀ state, r state state)
    (trans : ∀ {a b d}, r a b → r b d → r a d)
    (preserved : ∀ state, property state → ∀ reply : P.B (c state).1,
      r state ((c state).2 reply) ∧ property ((c state).2 reply))
    (initial : property first) : r first last ∧ property last := by
  induction trace with
  | nil => exact ⟨refl _, initial⟩
  | cons state reply tail ih =>
    obtain ⟨edge, next⟩ := preserved state initial reply
    obtain ⟨rest, final⟩ := ih next
    exact ⟨trans edge rest, final⟩

/-- A strictly decreasing natural rank bounds the number of consumed replies. -/
theorem Trace.rank_bound {first last : S} {events : List E}
    (trace : Trace c observe first events last) (rank : S → Nat)
    (decreases : ∀ state, ∀ reply : P.B (c state).1,
      rank ((c state).2 reply) < rank state) :
    events.length + rank last ≤ rank first := by
  induction trace with
  | nil => simp
  | cons state reply tail ih =>
    have decrease := decreases state reply
    simp only [List.length_cons]
    omega

/-- This rules out infinitely many returned replies, not an external operation
that never returns. Scheduling and cancellation remain interpreter obligations. -/
theorem no_infinite_replies (rank : S → Nat)
    (decreases : ∀ state, ∀ reply : P.B (c state).1,
      rank ((c state).2 reply) < rank state)
    (states : Nat → S) (replies : (n : Nat) → P.B (c (states n)).1)
    (successor : ∀ n, states (n + 1) = (c (states n)).2 (replies n)) : False := by
  have bounded : ∀ n, n + rank (states n) ≤ rank (states 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have decrease := decreases (states n) (replies n)
      rw [← successor n] at decrease
      omega
  have impossible := bounded (rank (states 0) + 1)
  omega

end PFunctor.Coalgebra
