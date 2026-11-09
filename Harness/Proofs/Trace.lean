import Harness.Proofs.Reachability

/-!
# Observed execution traces

Events record actual coalgebra requests and their dependent replies. This relation
does not implement a second runner: every edge is the continuation returned by
`step`. Administrative recovery, journal framing and external scheduling are
separate relations and obligations.
-/

namespace Harness

variable {app : Application}

structure ObservedStep (app : Application := Coding.application) where
  operation : Nat
  action : (Action app)
  reply : Reply action

def observe (state : (State app)) (response : Reply (step state).1) : ObservedStep app :=
  ⟨state.nextId, (step state).1, response⟩

abbrev ExecutionTrace := PFunctor.Coalgebra.Trace (step (app := app)) (observe (app := app))

theorem ExecutionTrace.append {first middle last : (State app)} {left right : List (ObservedStep app)}
    (a : ExecutionTrace first left middle) (b : ExecutionTrace middle right last) :
    ExecutionTrace first (left ++ right) last :=
  PFunctor.Coalgebra.Trace.append a b

theorem ExecutionTrace.reachable {id : String} {config : Config} {task : String}
    {first last : (State app)} {events : List (ObservedStep app)}
    (trace : ExecutionTrace first events last) (start : Reachable id config task first) :
    Reachable id config task last := by
  induction trace with
  | nil => exact start
  | cons state response tail ih => exact ih (.next start response)

theorem reachable_has_trace {id : String} {config : Config} {task : String} {state : (State app)}
    (reachable : Reachable id config task state) :
    ∃ events, ExecutionTrace (init id config task app) events state := by
  induction reachable with
  | initial => exact ⟨[], .nil _⟩
  | next prior response ih =>
    obtain ⟨events, trace⟩ := ih
    exact ⟨events ++ [observe _ response], trace.append
      (.cons (c := step) (observe := observe) _ response (.nil _))⟩

end Harness
