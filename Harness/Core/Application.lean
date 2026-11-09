import Harness.Core.Protocol

/-!
The pure application boundary. An application supplies a family of typed operations and replies,
their wire codecs, permission decisions, and conservative recovery rules. It cannot update the
session, grant approval, refund a reservation, or dispatch an effect. The engine owns those steps.

`ToolAPI.functor` is the polynomial functor for tool interactions alone. The harness adds model,
control, approval and terminal actions in `Effects`.
-/

namespace Harness
open Lean

inductive Decision where
  | allow | deny | ask
  deriving Repr, BEq, DecidableEq

/-- Recovery evidence may settle an operation; it cannot silently preserve uncertainty. -/
inductive Settled (α : Type) where
  | success (value : α)
  | failure (message : String)

def Settled.observation : Settled α → ToolObservation α
  | .success value => .success value
  | .failure message => .failure message

structure ToolAPI where
  Call : Type
  Result : Call → Type

/-- A statically installed application's pure contract. Values are frozen by executable identity;
session-specific data belongs in `Config.applicationData`, which transitions never change. -/
structure Application where
  id : String
  version : Nat
  Operation : Type
  operationRepr : Repr Operation
  operationDecEq : DecidableEq Operation
  operationToJson : ToJson Operation
  operationFromJson : FromJson Operation
  Result : Operation → Type
  resultToJson : (op : Operation) → ToJson (Result op)
  resultFromJson : (op : Operation) → FromJson (Result op)
  Witness : Type
  witnessRepr : Repr Witness
  witnessToJson : ToJson Witness
  witnessFromJson : FromJson Witness
  Resolution : Type
  resolutionToJson : ToJson Resolution
  resolutionFromJson : FromJson Resolution
  defaultInstructions : String
  schemas : Array Json
  decode : RawCall → Except String Operation
  name : Operation → String
  args : Operation → Json
  /-- Complete authority required by the operation, including disclosures during
  preparation. An empty list is denied. This declaration does not establish the
  behavior of its IO implementation; applications supply the corresponding laws. -/
  requiredCapabilities : Operation → List Capability.Access
  policy : Config → Operation → Decision
  render : (op : Operation) → Result op → ToolResult
  artifactRead : Operation → Option String := fun _ => none
  settledTimeout : Config → Operation → Bool := fun _ _ => false
  readOnly : Operation → Bool := fun _ => false
  mayAbandon : Operation → Bool := fun _ => false
  validateWitness : Operation → Witness → Except String Unit
  resolve : (op : Operation) → Option Witness → Resolution → Except String (Settled (Result op))
  operatorResolution : Resolution → Bool

instance (app : Application) : Repr app.Operation := app.operationRepr
instance (app : Application) : DecidableEq app.Operation := app.operationDecEq
instance (app : Application) : BEq app.Operation := instBEqOfDecidableEq
instance (app : Application) : ToJson app.Operation := app.operationToJson
instance (app : Application) : FromJson app.Operation := app.operationFromJson
instance (app : Application) (op : app.Operation) : ToJson (app.Result op) := app.resultToJson op
instance (app : Application) (op : app.Operation) : FromJson (app.Result op) := app.resultFromJson op
instance (app : Application) : Repr app.Witness := app.witnessRepr
instance (app : Application) : ToJson app.Witness := app.witnessToJson
instance (app : Application) : FromJson app.Witness := app.witnessFromJson
instance (app : Application) : ToJson app.Resolution := app.resolutionToJson
instance (app : Application) : FromJson app.Resolution := app.resolutionFromJson

/-- The core supplies correlation IDs. A domain decoder can only select the operation. -/
structure Call (app : Application) where
  id : String
  operation : app.Operation
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

abbrev Application.toolAPI (app : Application) : ToolAPI :=
  {Call := Call app, Result := fun call => app.Result call.operation}

def ToolObservation.map (f : α → β) : ToolObservation α → ToolObservation β
  | .success value => .success (f value)
  | .failure message => .failure message
  | .timedOut output => .timedOut (output.map f)
  | .interrupted message output => .interrupted message (output.map f)
  | .uncertain message output => .uncertain message (output.map f)

end Harness
