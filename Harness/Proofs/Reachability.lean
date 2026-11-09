import Harness.Core.Transition
import Harness.Theory.Coalgebra

/-! Reachability of the executable harness, with generic coalgebra invariant
lifting. This foundation does not depend on any particular safety property. -/

namespace Harness

variable {app : Application}

/-- Reachability starts at the executable initializer and follows typed replies. -/
inductive Reachable (id : String) (cfg : Config) (task : String) : (State app) → Prop where
  | initial : Reachable id cfg task (init id cfg task app)
  | next {s : (State app)} : Reachable id cfg task s → (r : Reply (step s).fst) →
      Reachable id cfg task ((step s).snd r)

theorem Reachable.to_reflTransGen {id : String} {cfg : Config} {task : String} {s : (State app)}
    (reachable : Reachable id cfg task s) :
    Relation.ReflTransGen (PFunctor.Coalgebra.Next step) (init id cfg task app) s := by
  induction reachable with
  | initial => exact .refl
  | next prior reply ih => exact ih.tail ⟨reply, rfl⟩

/-- Harness invariants supply initialization and one-step preservation; the
extension to all reachable states is a general polynomial-coalgebra fact. -/
theorem Reachable.invariant {id : String} {cfg : Config} {task : String} {s : (State app)}
    (reachable : Reachable id cfg task s) {property : (State app) → Prop}
    (initial : property (init id cfg task app))
    (preserved : ∀ state, property state → ∀ reply : Reply (step state).1,
      property ((step state).2 reply)) : property s := by
  apply PFunctor.Coalgebra.invariant (c := step) ?_ reachable.to_reflTransGen initial
  intro state valid
  exact (PFunctor.liftp_iff' property _ _).mpr (preserved state valid)

end Harness
