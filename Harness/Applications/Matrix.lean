import Harness.Core.Coding

/-! Matrix supplies frozen role authority and a protected tool runtime. The shared
engine still owns admission, budgets, operation identity and durable ordering. -/
namespace Harness.Matrix
open Lean

inductive BuildAction where
  | submit | wait | logs | cancel
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

inductive SubmissionKind where
  | selection | review | environmentRepair
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

def SubmissionKind.name : SubmissionKind → String
  | .selection => "submit_selection"
  | .review => "submit_review"
  | .environmentRepair => "submit_environment_repair"

def SubmissionKind.argument : SubmissionKind → String
  | .selection => "selection_json"
  | .review => "verdict_json"
  | .environmentRepair => "proposal_json"

def SubmissionKind.maxBytes : SubmissionKind → Nat
  | .review => 65536
  | _ => 32768

structure BuildArgs where
  action : BuildAction := .submit
  project : Option String := none
  build_id : Option String := none
  wait : Option Bool := none
  wait_timeout_seconds : Option JsonNumber := none
  build_timeout_seconds : Option Nat := none
  cpus : Option Nat := none
  memory_gb : Option JsonNumber := none
  cache : Option Bool := none
  reuse_cache : Option Bool := none
  cache_from : Option String := none
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

private def optionalField [ToJson α] (key : String) (value : Option α) : List (String × Json) :=
  value.toList.map fun item => (key, toJson item)

/-- Preserve absence: the pinned build client uses operator defaults and treats
explicit resource/cache options differently when attributing reusable builds. -/
def BuildArgs.nativeJson (args : BuildArgs) : Json := Json.mkObj <|
  [("action", toJson args.action)] ++ optionalField "project" args.project ++
  optionalField "build_id" args.build_id ++ optionalField "wait" args.wait ++
  optionalField "wait_timeout_seconds" args.wait_timeout_seconds ++
  optionalField "build_timeout_seconds" args.build_timeout_seconds ++
  optionalField "cpus" args.cpus ++ optionalField "memory_gb" args.memory_gb ++
  optionalField "cache" args.cache ++ optionalField "reuse_cache" args.reuse_cache ++
  optionalField "cache_from" args.cache_from

inductive Operation where
  | coding (operation : ToolOp)
  | lakeBuild (args : BuildArgs)
  | submit (kind : SubmissionKind) (payload : String)
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

def validHex (length : Nat) (value : String) : Bool :=
  value.length == length && value.toList.all (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f'))

def validSeconds (value : JsonNumber) : Bool :=
  let number := value.toFloat
  number.isFinite && 0.0 < number && number ≤ 86400.0

def validMemory (value : JsonNumber) : Bool :=
  let number := value.toFloat
  number.isFinite && 7.0 ≤ number && number ≤ 103.75

def validateBuildArgs (args : BuildArgs) : Except String Unit := do
  unless args.wait_timeout_seconds.all validSeconds do throw "invalid build wait limit"
  if args.action == .submit then
    unless args.build_id.isNone do throw "submit cannot name an existing build"
    unless args.project.all (fun path => Coding.safePath path && path.length ≤ 256) do
      throw "build project must be a bounded workspace-relative path"
    unless args.build_timeout_seconds.all (fun seconds => 60 ≤ seconds && seconds ≤ 7200) &&
        args.cpus.all (fun cpus => 1 ≤ cpus && cpus ≤ 30) && args.memory_gb.all validMemory &&
        args.cache_from.all (validHex 16) do throw "invalid build resource/cache bounds"
  else
    unless args.build_id.any (validHex 16) do throw "build action requires its exact backend ID"
    unless args.project.isNone && args.wait.isNone && args.build_timeout_seconds.isNone &&
        args.cpus.isNone && args.memory_gb.isNone && args.cache.isNone &&
        args.reuse_cache.isNone && args.cache_from.isNone do
      throw "submit-only arguments supplied to another build action"

def validateOperation : Operation → Except String Unit
  | .coding op => Coding.validateOperation op
  | .lakeBuild args => validateBuildArgs args
  | .submit kind payload => do
    unless !payload.trimAscii.toString.isEmpty && payload.utf8ByteSize ≤ kind.maxBytes do
      throw "submission must be a nonempty string within the role's byte bound"

def name : Operation → String
  | .coding op => ToolOp.name op
  | .lakeBuild _ => "lake_build"
  | .submit kind _ => kind.name

def args : Operation → Json
  | .coding op => ToolOp.args op
  | .lakeBuild args => args.nativeJson
  | .submit kind payload => Json.mkObj [(kind.argument, toJson payload)]

private def submissionKind (name : String) : Option SubmissionKind :=
  if name == "submit_selection" then some .selection
  else if name == "submit_review" then some .review
  else if name == "submit_environment_repair" then some .environmentRepair else none

private def parseOperation (raw : RawCall) : Except String Operation := do
  let operation ← if raw.name == "lake_build" then do
      unless !raw.id.isEmpty do throw "empty tool call identity"
      let fields ← raw.input.getObj?
      let allowed := ["action", "project", "build_id", "wait", "wait_timeout_seconds",
        "build_timeout_seconds", "cpus", "memory_gb", "cache", "reuse_cache", "cache_from"]
      unless fields.toList.all (fun (key, _) => allowed.contains key) do throw "unknown build argument"
      pure (.lakeBuild (← fromJson? raw.input))
    else if let some kind := submissionKind raw.name then do
      unless !raw.id.isEmpty do throw "empty tool call identity"
      let fields ← raw.input.getObj?
      unless fields.size == 1 && fields.contains kind.argument do throw "submission requires its exact payload field"
      pure (.submit kind (← raw.input.getObjValAs? String kind.argument))
    else Operation.coding <$> Coding.decodeOperation raw
  return operation

def decodeOperation (raw : RawCall) : Except String Operation := do
  let operation ← parseOperation raw
  validateOperation operation
  return operation

structure Identity where
  executionId : String
  agentId : String
  turnId : String
  attemptId : String
  requestId : String
  sessionId : String
  operationId : Nat
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure BuildReceipt where
  identity : Identity
  action : BuildAction
  scope : String
  inputDigest : Option String
  uploadDigest : Option String
  backendBuildId : Option String
  backendBuildIds : Array String
  status : String
  effectSettled : Bool
  submissionUncertain : Bool
  nativeResult : String
  output : ToolResult
  deriving Repr, ToJson, FromJson

structure SubmissionReceipt where
  identity : Identity
  kind : SubmissionKind
  payload : String
  nativeResult : String
  output : ToolResult
  deriving Repr, ToJson, FromJson

structure Root where
  name : String
  path : String
  readOnly : Bool := true
  buildable : Bool := false
  deriving Repr, ToJson, FromJson

def Result : Operation → Type
  | .coding _ => ToolResult
  | .lakeBuild _ => BuildReceipt
  | .submit _ _ => SubmissionReceipt

instance (operation : Operation) : ToJson (Result operation) := by
  cases operation <;> simp only [Result] <;> infer_instance

def validIdentity (identity : Identity) : Bool :=
  [identity.executionId, identity.agentId, identity.turnId, identity.attemptId, identity.requestId].all
    (fun value => !value.isEmpty && value.utf8ByteSize ≤ 256 && !value.contains '\x00') &&
  !identity.sessionId.isEmpty && identity.sessionId.utf8ByteSize ≤ 4096 && !identity.sessionId.contains '\x00'

def validBuildReceipt (arguments : BuildArgs) (receipt : BuildReceipt) : Bool :=
  validIdentity receipt.identity && receipt.action == arguments.action &&
  (arguments.action == .submit || receipt.backendBuildId == arguments.build_id) &&
  receipt.inputDigest.all (validHex 64) && receipt.uploadDigest.all (validHex 64) &&
  receipt.backendBuildId.all (validHex 16) && !receipt.scope.isEmpty && receipt.scope.utf8ByteSize ≤ 4096 &&
  receipt.backendBuildIds.size ≤ 128 && receipt.backendBuildIds.all (validHex 16) &&
  receipt.backendBuildId.all (receipt.backendBuildIds.contains ·) &&
  ["refused", "accepted", "queued", "running", "succeeded", "failed", "cancelled", "unresolved", "logs"].contains receipt.status &&
  (receipt.status != "unresolved" || !receipt.effectSettled) &&
  (!receipt.submissionUncertain || !receipt.effectSettled) &&
  (!receipt.backendBuildId.isSome || arguments.action != .submit || receipt.inputDigest.isSome) &&
  receipt.nativeResult.utf8ByteSize ≤ 1024 * 1024

def validSubmissionReceipt (kind : SubmissionKind) (payload : String) (receipt : SubmissionReceipt) : Bool :=
  validIdentity receipt.identity && receipt.kind == kind && receipt.payload == payload &&
  receipt.nativeResult.utf8ByteSize ≤ 1024 * 1024

def decodeResult : (operation : Operation) → Json → Except String (Result operation)
  | .coding _, value => (fromJson? value : Except String ToolResult)
  | .lakeBuild arguments, value => do
    let receipt : BuildReceipt ← fromJson? value
    unless validBuildReceipt arguments receipt do throw "build receipt does not match the admitted operation"
    return receipt
  | .submit kind payload, value => do
    let receipt : SubmissionReceipt ← fromJson? value
    unless validSubmissionReceipt kind payload receipt do throw "submission receipt does not match the exact operation"
    return receipt

instance (operation : Operation) : FromJson (Result operation) := ⟨decodeResult operation⟩

def render : (op : Operation) → Result op → ToolResult
  | .coding _, result => result
  | .lakeBuild _, result => result.output
  | .submit _ _, result => result.output

structure Binding where
  version : Nat := 1
  executionId : String
  agentId : String
  turnId : String
  attemptId : String
  requestId : String
  role : String
  sessionPath : String
  checkoutRevision : String
  workspaceDevice : String
  workspaceInode : String
  deadlineEpochMs : Nat
  authorizationDigest : String
  bindingDigest : String
  serviceUrl : String := ""
  serviceCaller : String := ""
  allowedBuildIds : Array String := #[]
  workspace : String
  readOnly : Bool
  tools : Array String
  helperPath : String
  helperDigest : String
  nodePath : String
  nodeDigest : String
  resourceRoot : String
  resourceDigest : String
  roots : Array Root := #[]
  deriving Repr, ToJson, FromJson

def logicalRoot (path : String) : Option String :=
  let first := (Capability.normalizePath path).bind List.head?
  first.bind fun component =>
    if component.startsWith "@" then some (component.drop 1).toString else none

def operationPath : ToolOp → Option String
  | .listFiles args => some args.path
  | .readFile args => some args.path
  | .searchFiles args => some args.path
  | .editFile args => some args.path
  | .createFile args => some args.path
  | .runProcess _ | .readArtifact _ => none

def rootReadOnly (binding : Binding) (path : String) : Option Bool :=
  match logicalRoot path with
  | none => some binding.readOnly
  | some name => (binding.roots.find? (·.name == name)).map (·.readOnly)

private def metadataPath (path : String) : Bool :=
  ((Capability.normalizePath path).getD []).contains ".git"

def codingRoleTool : ToolOp → String
  | .listFiles _ => "ls"
  | .readFile _ | .readArtifact _ => "read"
  | .searchFiles _ => "grep"
  | .editFile _ => "edit"
  | .createFile _ => "write"
  | .runProcess _ => "bash"

def policy (config : Config) (operation : Operation) : Decision :=
  match (fromJson? config.applicationData : Except String Binding) with
  | .error _ => .deny
  | .ok binding =>
    let roleTool := match operation with
      | .coding op => codingRoleTool op
      | _ => name operation
    let enabled := binding.tools.contains roleTool ||
      (roleTool == "ls" && binding.tools.contains "find")
    if !enabled then .deny else match operation with
    | .coding (.editFile arguments) =>
      if !metadataPath arguments.path && rootReadOnly binding arguments.path == some false then .allow else .deny
    | .coding (.createFile arguments) =>
      if !metadataPath arguments.path && rootReadOnly binding arguments.path == some false then .allow else .deny
    | .coding (.runProcess arguments) => Coding.policy config (.runProcess arguments)
    | .coding op =>
      if (operationPath op).any (fun path => (rootReadOnly binding path).isNone) then .deny else .allow
    | .lakeBuild arguments =>
      if arguments.action == .submit then
        match logicalRoot (arguments.project.getD "lean") with
        | none => .allow
        | some name => if (binding.roots.find? (·.name == name)).any (·.buildable) then .allow else .deny
      else .allow
    | _ => .allow

def requiredCapabilities : Operation → List Capability.Access
  | .coding op => Coding.requiredCapabilities op
  | .lakeBuild args =>
    if args.action == .submit then
      [.read (.tree (args.project.getD "lean")), .resource "matrix" "lake_build" (.exact (args.project.getD "lean"))]
    else [.resource "matrix" "lake_build" (.exact (args.build_id.getD ""))]
  | .submit kind _ => [.resource "matrix" kind.name .all]

inductive Witness where
  | coding (evidence : Coding.EditWitness)
  | external (identity : Identity) (operation : Operation) (argumentsDigest : String) (inputDigest : Option String)
  deriving Repr, ToJson, FromJson

inductive Resolution where
  | coding (evidence : Coding.Resolution)
  | build (receipt : BuildReceipt)
  | submission (receipt : SubmissionReceipt)
  deriving Repr, ToJson, FromJson

def validateWitness (operation : Operation) (witness : Witness) : Except String Unit := do
  match operation, witness with
  | .coding op, .coding evidence => Coding.validateWitness op evidence
  | .lakeBuild _, .external identity original digest input | .submit _ _, .external identity original digest input =>
    unless original == operation && !identity.sessionId.isEmpty && !identity.requestId.isEmpty && validHex 64 digest &&
        input.all (validHex 64) do throw "external witness is not bound to a valid operation identity"
  | _, _ => throw "witness belongs to a different Matrix operation"

def resolve : (operation : Operation) → Option Witness → Resolution → Except String (Settled (Result operation))
  | .coding op, witness, .coding evidence => do
    let codingWitness := witness.bind fun | .coding value => some value | _ => none
    Coding.resolve op codingWitness evidence
  | .lakeBuild args, witness, .build receipt => do
    let some (.external identity original _ input) := witness | throw "build recovery requires its original durable witness"
    unless original == .lakeBuild args && (args.action != .submit || receipt.inputDigest == input) do
      throw "build receipt differs from the admitted arguments or source inputs"
    unless receipt.identity == identity && receipt.action == args.action && receipt.effectSettled &&
        !receipt.submissionUncertain && validBuildReceipt args receipt do
      throw "build effect is unresolved or belongs to another operation"
    return .success receipt
  | .submit kind payload, witness, .submission receipt => do
    let some (.external identity original _ _) := witness | throw "submission recovery requires its original durable witness"
    unless original == .submit kind payload do throw "submission witness belongs to another operation"
    unless receipt.identity == identity && validSubmissionReceipt kind payload receipt do
      throw "submission receipt does not match the exact bound operation"
    return .success receipt
  | _, _, _ => throw "resolution belongs to a different Matrix operation"

private def property (type description : String) : Json :=
  Json.mkObj [("type", toJson type), ("description", toJson description)]

private def toolSchema (toolName description : String) (properties : List (String × Json))
    (required : List String := []) : Json :=
  Json.mkObj [("name", toJson toolName), ("description", toJson description),
    ("input_schema", Json.mkObj [("type", toJson "object"), ("properties", Json.mkObj properties),
      ("required", toJson required), ("additionalProperties", toJson false)])]

def toolSchemas : Array Json := Coding.toolSchemas ++ #[
  toolSchema "lake_build"
    "Use the pinned Matrix build service for Lean compilation. Preserve an accepted build ID for wait/logs/cancel. Never resubmit an uncertain submission; the controller must reconcile it. Operator role scope, resources and remaining deadline apply."
    [("action", Json.mkObj [("type", toJson "string"),
        ("enum", toJson (#["submit", "wait", "logs", "cancel"] : Array String))]),
      ("project", property "string" "Workspace-relative project, default lean; submit only"),
      ("build_id", property "string" "Exact 16-character backend build ID; required except for submit"),
      ("wait", property "boolean" "Wait after submission, default true"),
      ("wait_timeout_seconds", property "number" "Positive wait limit within the operator's total build window"),
      ("build_timeout_seconds", property "integer" "Per-build timeout, 60..7200 seconds, within the operator ceiling"),
      ("cpus", property "integer" "Lower an explicitly configured CPU ceiling, 1..30"),
      ("memory_gb", property "number" "Lower an explicitly configured GiB ceiling, 7..103.75"),
      ("cache", property "boolean" "Save project cache, default true"),
      ("reuse_cache", property "boolean" "Reuse compatible cache, default true"),
      ("cache_from", property "string" "Exact compatible donor build ID; submit only")]] ++
  (#[SubmissionKind.selection, .review, .environmentRepair]).map fun kind =>
    toolSchema kind.name
      "Submit the exact structured decision as the only tool call in this response, once after inspection. The controller validates the exact role, request and candidate after the turn settles. After submission, finish without further tools."
      [(kind.argument, property "string" "Complete JSON object serialized as a string; no Markdown or prose")]
      [kind.argument]

def schemasFor (config : Config) : Array Json :=
  match (fromJson? config.applicationData : Except String Binding) with
  | .error _ => #[]
  | .ok binding => toolSchemas.filter fun schema =>
    let toolName := (schema.getObjValAs? String "name").toOption.getD ""
    let roleTool := match toolName with
      | "list" => "ls"
      | "search" => "grep"
      | "create" => "write"
      | "process" => "bash"
      | "artifact" => "read"
      | other => other
    (binding.tools.contains roleTool || (roleTool == "ls" && binding.tools.contains "find")) &&
      !(binding.readOnly && (roleTool == "edit" || roleTool == "write")) &&
      !(roleTool == "bash" && config.commands == .deny)

def application : Application where
  id := "matrix"
  version := 1
  Operation := Operation
  operationRepr := inferInstance
  operationDecEq := inferInstance
  operationToJson := inferInstance
  operationFromJson := inferInstance
  Result := Result
  resultToJson := fun _ => inferInstance
  resultFromJson := fun _ => inferInstance
  Witness := Witness
  witnessRepr := inferInstance
  witnessToJson := inferInstance
  witnessFromJson := inferInstance
  Resolution := Resolution
  resolutionToJson := inferInstance
  resolutionFromJson := inferInstance
  defaultInstructions := "Work within the frozen Matrix role and workspace. Use lake_build for Lean compilation; preserve build identities and never repeat an uncertain submission. Structured decisions require their exact submission tool. After submitting, finish without further tools."
  schemas := toolSchemas
  schemasFor := schemasFor
  decode := decodeOperation
  name := name
  args := args
  requiredCapabilities := requiredCapabilities
  policy := policy
  render := render
  artifactRead := fun | .coding (.readArtifact args) => some args.id | _ => none
  settledTimeout := fun config operation => config.executionProfile == .bubblewrap &&
    match operation with | .coding (.runProcess _) => true | _ => false
  readOnly := fun
    | .coding op => Coding.application.readOnly op
    | .lakeBuild _ => false
    | .submit _ _ => false
  mayAbandon := fun | .coding op => Coding.application.mayAbandon op | _ => false
  validateWitness := validateWitness
  resolve := resolve
  operatorResolution := fun
    | .coding evidence => Coding.application.operatorResolution evidence
    | _ => false

end Harness.Matrix
