import Harness.Core.Coding

/-!
Whole-batch admission and exact-action authorization shared by every application. The application
only decodes an operation and classifies its permission; call IDs, duplicate detection and grants
are controlled here. The coding decoder remains available through compatibility abbreviations.
-/

namespace Harness
open Lean

abbrev safePath := Coding.safePath
abbrev decodeOperation := Coding.decodeOperation

/-- The application decoder cannot change the provider's correlation ID. -/
def decodeCall (raw : RawCall) (app : Application := Coding.application) : Except String (Call app) := do
  if raw.id.isEmpty then throw "empty tool call identity"
  let operation ← app.decode raw
  return ⟨raw.id, operation⟩

/-- Reject the entire batch before accepting any assistant tool-use message. -/
def validateBatch (cfg : Config) (seen : List String) (calls : List RawCall)
    (app : Application := Coding.application) : Except String (List (Call app)) := do
  if calls.isEmpty then throw "tool-use response contained no calls"
  if calls.length > cfg.maxBatchCalls then throw "tool batch limit exceeded"
  let (_, result) ← calls.foldlM (init := (seen, [])) fun (ids, acc) raw => do
    if ids.contains raw.id then throw "duplicate tool call identity"
    let call ← decodeCall raw app
    return (raw.id :: ids, acc ++ [call])
  return result

variable {app : Application}

/-- Approval policy before the hard resource ceiling is applied. -/
def approvalPolicy (cfg : Config) (call : Call app) : Decision :=
  match cfg.toolPolicy, app.policy cfg call.operation with
  | .deny, _ | _, .deny => .deny
  | .ask, _ | _, .ask => .ask
  | .allow, .allow => .allow

/-- Every declared capability must lie inside every frozen ceiling. The model
cannot supply the declaration, and a human approval cannot override this guard. -/
def capabilitiesPermit (cfg : Config) (call : Call app) : Bool :=
  Capability.permitsAll cfg.capabilityPolicy (app.requiredCapabilities call.operation)

/-- Resource ceilings and the session-wide approval policy can only restrict
the application policy. They never turn an existing denial into an approval. -/
def policy (cfg : Config) (call : Call app) : Decision :=
  if capabilitiesPermit cfg call then approvalPolicy cfg call else .deny

/-- Grants bind to the complete typed call, including its ID and arguments. -/
def authorized (cfg : Config) (grant : Option (Call app)) (call : Call app) : Bool :=
  decide (policy cfg call = .allow) || (decide (policy cfg call = .ask) && decide (grant = some call))

end Harness
