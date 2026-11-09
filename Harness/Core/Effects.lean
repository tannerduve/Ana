import Harness.Core.Context
import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Effect Signatures

Describes harness interaction as a polynomial functor. `ToolAPI` abstracts tool calls and their
result types. `Effect` lists the operations: control, model, tool, ask, wait and finish.
`Response` assigns each operation its observation type. A `finish` effect has no reply.

`InteractionF` is generic over `ToolAPI`. `Action`, `Reply` and `HarnessF` fix it to the
concrete `CodingAPI`, which `step` uses. `actionToJson`, `replyToJson` and `replyFromJson`
serialize these operations and replies for journals and adapters.
-/

namespace Harness
open Lean

structure ToolAPI where
  Call : Type
  Result : Call → Type

abbrev CodingAPI : ToolAPI := {Call := ToolCall, Result := fun _ => ToolResult}

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
abbrev Action := Effect CodingAPI
abbrev Reply := Response CodingAPI
abbrev HarnessF := InteractionF CodingAPI

def actionToJson : Action → Json
  | .control => Json.mkObj [("kind", toJson "control")]
  | .model r => Json.mkObj [("kind", toJson "model"), ("request", toJson r)]
  | .tool c => Json.mkObj [("kind", toJson "tool"), ("call", toJson c)]
  | .ask c => Json.mkObj [("kind", toJson "ask"), ("call", toJson c)]
  | .wait ms => Json.mkObj [("kind", toJson "wait"), ("milliseconds", toJson ms)]
  | .finish o => Json.mkObj [("kind", toJson "finish"), ("outcome", toJson o)]

def replyToJson : (a : Action) → Reply a → Json
  | .control, r => toJson r
  | .model _, r => toJson r
  | .tool _, r => toJson r
  | .ask _, r => toJson r
  | .wait _, r => toJson r
  | .finish _, r => nomatch r

def replyFromJson : (a : Action) → Json → Except String (Reply a)
  | .control, j => fromJson? j
  | .model _, j => fromJson? j
  | .tool _, j => fromJson? j
  | .ask _, j => fromJson? j
  | .wait _, j => fromJson? j
  | .finish _, _ => .error "terminal operations have no reply"

end Harness
