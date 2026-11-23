import Harness.Applications.Matrix
import Harness.Applications.CodingIO
import Harness.Adapter.JsonBounds

/-! Trusted Matrix interpretation. Native clients remain outside model process
authority. The runner journals the witness before this adapter dispatches them. -/
namespace Harness.MatrixIO
open Lean Matrix

private def binding (config : Config) : IO Binding := IO.ofExcept (fromJson? config.applicationData)

private def readBytes (path : String) (limit : Nat := 1024 * 1024) : IO ByteArray := do
  let file := System.FilePath.mk path
  let some name := file.fileName | throw <| IO.userError "invalid Matrix resource path"
  Native.withFD (Native.openDir (file.parent.getD ".").toString) fun parent =>
    Native.withFD (Native.openReadAt parent name) fun fd => do
      let info ← Native.stat fd
      unless info.kind == 1 && info.size ≤ limit do throw <| IO.userError "invalid bounded Matrix resource"
      FilesystemIO.readBounded fd limit

private def readJson (path : String) : IO Json := do
  let some text := String.fromUTF8? (← readBytes path) | throw <| IO.userError "Matrix record is not UTF-8"
  IO.ofExcept (JsonBounds.parse text)

private def validateIdentity (session : String) (config : Config) : IO Unit := do
  let b ← binding config
  let (actualSession, workspace) ← ApplicationIO.validateSessionWorkspace session config.workspace
  unless b.version == 1 && b.workspace == workspace && config.workspace == workspace &&
      b.sessionPath == actualSession && config.executionProfile == .bubblewrap do
    throw <| IO.userError "Matrix requires its frozen session, workspace and isolated execution profile"
  Native.withFD (Native.openDir workspace) fun fd => do
    let info ← Native.stat fd
    unless toString info.device == b.workspaceDevice && toString info.inode == b.workspaceInode do
      throw <| IO.userError "Matrix workspace directory identity changed"
  unless (← readJson (b.resourceRoot ++ "/ana-binding.json")) == config.applicationData do
    throw <| IO.userError "Matrix binding differs from the frozen application configuration"
  unless (← Native.sha256 (← readBytes b.helperPath)) == b.helperDigest &&
      (← Native.sha256 (← readBytes b.nodePath (256 * 1024 * 1024))) == b.nodeDigest &&
      (← Native.sha256 (← readBytes (b.resourceRoot ++ "/ana-resources.json"))) == b.resourceDigest do
    throw <| IO.userError "pinned Matrix executable or resources changed"
  let some key ← IO.getEnv "MATRIX_ANA_SESSION_KEY"
    | throw <| IO.userError "only the owning live Matrix execution can reopen this session"
  unless (← Native.sha256 key.toUTF8) == b.authorizationDigest do
    throw <| IO.userError "Matrix session authorization changed"
  for root in b.roots do
    let (_, canonical) ← ApplicationIO.validateSessionWorkspace session root.path
    unless canonical == root.path && root.name != "" do
      throw <| IO.userError "Matrix resource root identity changed"

private def identity (b : Binding) (sessionId : String) (operationId : Nat) : Identity :=
  {executionId := b.executionId, agentId := b.agentId, turnId := b.turnId,
   attemptId := b.attemptId, requestId := b.requestId, sessionId, operationId}

private def request (config : Config) (context : ApplicationIO.OperationContext)
    (operation : Operation) (mode : String) : IO Json := do
  let b ← binding config
  let remaining := context.timeoutMs - ((← IO.monoMsNow) - context.startedMs)
  if remaining == 0 then throw <| IO.userError "Matrix preparation exhausted the operation allowance"
  let input := Json.mkObj [("version", toJson (1 : Nat)), ("mode", toJson mode),
    ("sessionPath", toJson context.session), ("identity", toJson (identity b context.sessionId context.operationId)),
    ("tool", toJson (Matrix.name operation)), ("argumentsText", toJson (Matrix.args operation).compress),
    ("batchTools", toJson context.batchTools), ("timeoutMs", toJson remaining)]
  let key ← IO.getEnv "MATRIX_ANA_SESSION_KEY"
  let home ← IO.getEnv "HOME"
  let path ← IO.getEnv "PATH"
  let result ← ProcessIO.capture {
    cmd := b.nodePath, args := #[b.helperPath]
    cwd := some b.resourceRoot, input := input.compress.toUTF8
    timeoutMs := remaining, invocationDeadlineMs := context.invocationDeadlineMs
    cancelPath := context.cancelPath, stdoutBytes := 1024 * 1024, stderrBytes := 4096
    environment := some #[ ("MATRIX_ANA_SESSION_KEY", key), ("HOME", home), ("PATH", path),
      ("LBAAS_URL", some b.serviceUrl), ("LBAAS_USER_EMAIL", some b.serviceCaller) ]}
  unless result.status == .completed && result.exitCode == some 0 && result.stdoutTotal ≤ 1024 * 1024 do
    throw <| IO.userError "Matrix receipt unavailable; retain the durable intent and reconcile before retry"
  let some text := String.fromUTF8? result.stdout | throw <| IO.userError "Matrix receipt is not UTF-8"
  IO.ofExcept (JsonBounds.parse text)

private def guard (config : Config) (context : ApplicationIO.OperationContext) (operation : Operation) : IO Unit := do
  let _ ← request config context operation "guard"

private def rooted (b : Binding) (operation : ToolOp) : IO (String × ToolOp) := do
  let path := (Matrix.operationPath operation).getD "."
  match Matrix.logicalRoot path with
  | none => return (b.workspace, operation)
  | some name =>
    let some root := b.roots.find? (·.name == name) | throw <| IO.userError "undeclared Matrix resource alias"
    let some normalized := Capability.normalizePath path | throw <| IO.userError "invalid resource path"
    let parts := normalized.drop 1
    let relative := if parts.isEmpty then "." else String.intercalate "/" parts
    let operation := match operation with
      | .listFiles a => .listFiles {a with path := relative}
      | .readFile a => .readFile {a with path := relative}
      | .searchFiles a => .searchFiles {a with path := relative}
      | .editFile a => .editFile {a with path := relative}
      | .createFile a => .createFile {a with path := relative}
      | other => other
    return (root.path, operation)

private def prepare (config : Config) (context : ApplicationIO.OperationContext) (call : Call Matrix.application) :
    IO (Option Witness) := do
  guard config context call.operation
  match call.operation with
  | .coding op =>
    let (workspace, operation) ← rooted (← binding config) op
    let evidence ← CodingIO.runtime.prepare {config with workspace, applicationData := .null} context {id := call.id, operation}
    return evidence.map fun value => .coding {value with path := (Matrix.operationPath op).getD value.path}
  | operation =>
    let evidence ← request config context operation "prepare"
    let digest ← IO.ofExcept (evidence.getObjValAs? String "argumentsDigest")
    let input ← IO.ofExcept (evidence.getObjValAs? (Option String) "inputDigest")
    return some (.external (identity (← binding config) context.sessionId context.operationId) operation digest input)

private def resultText (native : Json) (maximum : Nat) : String :=
  let parts := (native.getObjValAs? (Array Json) "content").toOption.getD #[]
  let text := String.intercalate "\n" (parts.toList.filterMap fun part => (part.getObjValAs? String "text").toOption)
  FilesystemIO.utf8Prefix text.toUTF8 maximum

private def externalResult (config : Config) (context : ApplicationIO.OperationContext)
    (operation : Operation) (record : Json) : IO (Matrix.Result operation) := do
  let b ← binding config
  let actualIdentity : Identity ← IO.ofExcept (record.getObjValAs? Identity "identity")
  unless actualIdentity == identity b context.sessionId context.operationId do
    throw <| IO.userError "Matrix receipt identity mismatch"
  let native ← IO.ofExcept (record.getObjVal? "nativeResult")
  let isError := (native.getObjValAs? Bool "isError").toOption.getD false
  let output : ToolResult := {text := resultText native config.maxToolOutputBytes, exitCode := some (if isError then 1 else 0)}
  match h : operation with
  | .coding _ => throw <| IO.userError "coding operation has no external receipt"
  | .lakeBuild args =>
    let details := (native.getObjVal? "details").toOption.getD .null
    let ids ← IO.ofExcept (record.getObjValAs? (Array String) "buildIds")
    let id := (details.getObjValAs? String "build_id").toOption.orElse fun _ => ids.back?
    let uncertain := (details.getObjValAs? Bool "submission_uncertain").toOption.getD false
    let admitted := (record.getObjValAs? Bool "admitted").toOption.getD false
    let status := (details.getObjValAs? String "status").toOption.getD
      (if uncertain then "unresolved" else if args.action == .logs then "logs" else if id.isSome then "accepted" else "refused")
    let settled := !uncertain && (args.action == .logs || ["succeeded", "failed", "cancelled"].contains status || (!admitted && id.isNone))
    let receipt : BuildReceipt := {
      identity := actualIdentity, action := args.action
      scope := ← IO.ofExcept (record.getObjValAs? String "scope")
      inputDigest := ← IO.ofExcept (record.getObjValAs? (Option String) "inputDigest")
      uploadDigest := ← IO.ofExcept (record.getObjValAs? (Option String) "uploadDigest")
      backendBuildId := id, backendBuildIds := ids, status, effectSettled := settled
      submissionUncertain := uncertain, nativeResult := native.compress, output}
    unless Matrix.validBuildReceipt args receipt do throw <| IO.userError "invalid Matrix build receipt"
    return h.symm ▸ receipt
  | .submit kind payload =>
    let receipt : SubmissionReceipt := {identity := actualIdentity, kind, payload, nativeResult := native.compress, output}
    unless Matrix.validSubmissionReceipt kind payload receipt do throw <| IO.userError "invalid Matrix submission receipt"
    return h.symm ▸ receipt

private def operationContext (context : ToolContext) : IO ApplicationIO.OperationContext := do
  return {
    session := context.sessionPath, sessionId := context.sessionId, operationId := context.operationId
    batchTools := context.batchTools, startedMs := ← IO.monoMsNow, timeoutMs := context.timeoutMs
    invocationDeadlineMs := context.invocationDeadlineMs, cancelPath := context.cancelPath}

private def execute (config : Config) (context : ToolContext) (id : String) (op : Operation) :
    IO (ToolObservation (Matrix.Result op)) := do
  match h : op with
  | .coding op =>
    let started ← IO.monoMsNow
    guard config (← operationContext context) (.coding op)
    let context := {context with timeoutMs := context.timeoutMs - ((← IO.monoMsNow) - started)}
    let b ← binding config
    let (workspace, operation) ← rooted b op
    let mounts := b.roots.map fun root => {name := root.name, path := root.path, readOnly := root.readOnly : ResourceMount}
    let context := {context with workspace, workspaceReadOnly := b.readOnly, resourceMounts := mounts}
    let observation ← match operation with
      | .runProcess args => ProcessIO.run context args
      | _ => FilesystemIO.run context {id, operation}
    return h.symm ▸ observation
  | .lakeBuild args =>
    try
      let context ← operationContext context
      let record ← request config context (.lakeBuild args) "execute"
      let receipt ← externalResult config context (.lakeBuild args) record
      if receipt.submissionUncertain || receipt.status == "unresolved" then
        return h.symm ▸ (.uncertain "Matrix build submission requires reconciliation; automatic replay refused" (some receipt))
      return h.symm ▸ (.success receipt)
    catch _ => return .uncertain "Matrix external operation requires reconciliation; automatic replay refused"
  | .submit kind payload =>
    try
      let context ← operationContext context
      let record ← request config context (.submit kind payload) "execute"
      return h.symm ▸ (.success (← externalResult config context (.submit kind payload) record))
    catch _ => return .uncertain "Matrix external operation requires reconciliation; automatic replay refused"

private def reconcile (config : Config) (context : ApplicationIO.OperationContext) (call : Call Matrix.application)
    (witness : Option Witness) : IO Resolution := do
  match call.operation with
  | .coding op =>
    let (workspace, operation) ← rooted (← binding config) op
    let evidence := witness.bind fun | .coding value => some {value with path := (Matrix.operationPath operation).getD value.path} | _ => none
    return .coding (← CodingIO.runtime.reconcile {config with workspace, applicationData := .null} context {id := call.id, operation} evidence)
  | .lakeBuild args =>
    let record ← request config context (.lakeBuild args) "reconcile"
    return .build (← externalResult config context (.lakeBuild args) record)
  | .submit kind payload =>
    let record ← request config context (.submit kind payload) "reconcile"
    return .submission (← externalResult config context (.submit kind payload) record)

def runtime : ApplicationIO.Runtime Matrix.application where
  prepareConfig := fun config => do
    let b ← binding config
    unless config.workspace == b.workspace do throw <| IO.userError "Matrix checkout differs from its frozen authority"
    return config
  validateIdentity := validateIdentity
  validate := fun session config => do
    validateIdentity session config
    ProcessIO.validateSandbox config.workspace session config.executionProfile config.toolchainRoots
  prepare := prepare
  execute := fun config context call => execute config context call.id call.operation
  reconcile := reconcile

end Harness.MatrixIO
