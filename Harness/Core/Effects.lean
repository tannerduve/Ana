import Harness.Core.Context
import Mathlib.Data.PFunctor.Univariate.Basic

/-!
Defines the polynomial functor $F(X) = \sum_{a} (\mathsf{Reply}(a) \to X)$ as a Mathlib `PFunctor`.
`Effect` lists control, model, tool, ask, wait and finish; `Response` gives each its observation
type, with no reply for finish. `HarnessF app` installs an application's typed tool interface;
`ToolAPI.functor` describes tools alone. JSON reply decoding is indexed by the exact emitted action.
-/

namespace Harness
open Lean

/-- Calls are shapes; typed observations are positions in the tool container. -/
def ToolAPI.functor (T : ToolAPI) : PFunctor :=
  {A := T.Call, B := fun call => ToolObservation (T.Result call)}

abbrev CodingAPI : ToolAPI := Coding.application.toolAPI

inductive Effect (T : ToolAPI) where
  | control
  | model (request : ModelRequest)
  | tool (call : T.Call)
  | ask (call : T.Call)
  | wait (milliseconds : Nat)
  | finish (outcome : Outcome)

abbrev Response (T : ToolAPI) : Effect T → Type
  | .control => ControlObservation
  | .model _ => ModelObservation
  | .tool call => ToolObservation (T.Result call)
  | .ask _ => ApprovalObservation
  | .wait _ => WaitObservation
  | .finish _ => Empty

abbrev InteractionF (T : ToolAPI) : PFunctor := {A := Effect T, B := Response T}
abbrev Action (app : Application := Coding.application) := Effect app.toolAPI
abbrev Reply {app : Application} := Response app.toolAPI
abbrev HarnessF (app : Application := Coding.application) := InteractionF app.toolAPI

variable {app : Application}

def actionToJson : Action app → Json
  | .control => Json.mkObj [("kind", toJson "control")]
  | .model r => Json.mkObj [("kind", toJson "model"), ("request", toJson r)]
  | .tool c => Json.mkObj [("kind", toJson "tool"), ("call", toJson c)]
  | .ask c => Json.mkObj [("kind", toJson "ask"), ("call", toJson c)]
  | .wait ms => Json.mkObj [("kind", toJson "wait"), ("milliseconds", toJson ms)]
  | .finish o => Json.mkObj [("kind", toJson "finish"), ("outcome", toJson o)]

def replyToJson : (a : Action app) → Reply a → Json
  | .control, r => toJson r
  | .model _, r => toJson r
  | .tool _, r => toJson r
  | .ask _, r => toJson r
  | .wait _, r => toJson r
  | .finish _, r => nomatch r

def replyFromJson : (a : Action app) → Json → Except String (Reply a)
  | .control, j => fromJson? j
  | .model _, j => fromJson? j
  | .tool _, j => fromJson? j
  | .ask _, j => fromJson? j
  | .wait _, j => fromJson? j
  | .finish _, _ => .error "terminal operations have no reply"

end Harness
