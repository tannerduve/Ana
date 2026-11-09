import Harness.Core.Application
import Harness.Applications.Coding.Schemas

/-! The coding application's closed operation family, decoder and conservative
recovery rules. This pure instance supplies no filesystem or process IO; the
shared core owns grants, reservations, history and advancement. -/

namespace Harness.Coding
open Lean

/-- Lexical guard only. The filesystem adapter also rejects symlinks. -/
def safePath (p : String) : Bool :=
  !p.isEmpty && !p.startsWith "/" && !(p.splitOn "/").contains ".." &&
    !(p.toList.contains '\x00')

/-- Argument constraints shared by model admission and the application contract. -/
def validateOperation (op : ToolOp) : Except String Unit := do
  match op with
  | .listFiles a =>
    if !safePath a.path || a.limit == 0 || a.limit > 2000 then throw "invalid list bounds/path"
  | .readFile a =>
    if !safePath a.path || a.startLine == 0 || a.endLine < a.startLine || a.endLine - a.startLine > 2000 then
      throw "invalid read bounds/path"
  | .searchFiles a =>
    if !safePath a.path || a.query.isEmpty || a.limit == 0 || a.limit > 2000 then throw "invalid search bounds/path"
  | .editFile a =>
    if !safePath a.path || a.old.isEmpty || a.expectedSha256.length != 64 then throw "invalid edit/preimage/path"
  | .createFile a =>
    if !safePath a.path then throw "invalid create path"
  | .runProcess a =>
    if !safePath a.cwd || a.argv.isEmpty || a.argv[0]!.isEmpty then throw "invalid process arguments/path"
  | .readArtifact a =>
    if a.id.isEmpty || a.id.length > 80 || a.length == 0 || a.length > 65536 then
      throw "invalid artifact identity or range length (1..65536 bytes)"

def parseOperation (raw : RawCall) : Except String ToolOp := do
  if raw.id.isEmpty then throw "empty tool call identity"
  let allowed := match raw.name with
    | "list" => ["path", "limit"]
    | "read" => ["path", "startLine", "endLine"]
    | "search" => ["query", "path", "limit", "caseSensitive"]
    | "edit" => ["path", "old", "new", "expectedSha256"]
    | "create" => ["path", "content", "overwrite"]
    | "process" => ["argv", "cwd"]
    | "artifact" => ["id", "offset", "length"]
    | _ => []
  let fields ← raw.input.getObj?
  if fields.toList.any (fun (k, _) => !allowed.contains k) then throw "unknown tool argument"
  let defaults : List (String × Json) := match raw.name with
    | "list" => [("path", toJson "."), ("limit", toJson (200 : Nat))]
    | "read" => [("startLine", toJson (1 : Nat)), ("endLine", toJson (200 : Nat))]
    | "search" => [("path", toJson "."), ("limit", toJson (100 : Nat)), ("caseSensitive", toJson true)]
    | "create" => [("overwrite", toJson false)]
    | "process" => [("cwd", toJson ".")]
    | "artifact" => [("offset", toJson (0 : Nat)), ("length", toJson (4096 : Nat))]
    | _ => []
  let input := Json.mkObj (defaults ++ fields.toList)
  let op ← match raw.name with
    | "list" => ToolOp.listFiles <$> fromJson? input
    | "read" => ToolOp.readFile <$> fromJson? input
    | "search" => ToolOp.searchFiles <$> fromJson? input
    | "edit" => ToolOp.editFile <$> fromJson? input
    | "create" => ToolOp.createFile <$> fromJson? input
    | "process" => ToolOp.runProcess <$> fromJson? input
    | "artifact" => ToolOp.readArtifact <$> fromJson? input
    | _ => throw s!"unknown tool: {raw.name}"
  return op

def decodeOperation (raw : RawCall) : Except String ToolOp := do
  let op ← parseOperation raw
  validateOperation op
  return op

/-- Durable edit evidence is specific to the coding application. -/
structure EditWitness where
  version : Nat := 1
  path : String
  preimage : String
  postimage : String
  deriving Repr, ToJson, FromJson

inductive Resolution where
  | editPostimage (observed : String)
  | processCompleted (exitCode : Int) (note : String)
  | processAbandoned (note : String)
  deriving Repr, ToJson, FromJson

private def validHash (hash : String) : Bool :=
  hash.length == 64 && hash.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

def validateWitness (operation : ToolOp) (witness : EditWitness) : Except String Unit := do
  match operation with
  | .editFile args =>
    unless witness.version == 1 && witness.path == args.path &&
        witness.preimage == args.expectedSha256 && validHash witness.preimage && validHash witness.postimage do
      throw "edit witness does not match admitted operation"
  | _ => throw "edit witness attached to a different operation"

private def validNote (note : String) : Bool :=
  !note.trimAscii.toString.isEmpty && note.utf8ByteSize ≤ 2048

def resolve (operation : ToolOp) (witness : Option EditWitness)
    (resolution : Resolution) : Except String (Settled ToolResult) := do
  match operation, resolution with
  | .editFile _, .editPostimage observed =>
    let some witness := witness | throw "edit intent has no preimage/postimage witness"
    validateWitness operation witness
    unless observed == witness.postimage do throw "observed file identity does not match intended postimage"
    return .success {text := s!"reconciled {witness.path}: current contents match intended postimage; execution count is unknown", sha256 := some observed}
  | .runProcess _, .processCompleted code note =>
    unless validNote note && 0 ≤ code && code ≤ 255 do
      throw "completion requires an exit code in 0..255 and a nonempty note of at most 2048 bytes"
    return .success {text := s!"Operator-reported completion; not independently verified: {note}", exitCode := some code}
  | .runProcess _, .processAbandoned note =>
    unless validNote note do throw "abandonment requires a nonempty note of at most 2048 bytes"
    return .failure s!"Operator abandoned uncertain command; prior effects remain unknown and the command was not repeated: {note}"
  | _, _ => throw "resolution does not apply to the unresolved operation"

/-- Conservative authority for the dedicated tool's entire observable scope. Listing and
searching disclose a subtree; reading also exposes full-file identity metadata. Editing reads
the preimage before writing. Process authority names an invocation, not its IO footprint:
argv/cwd permissions do not constrain the files or other effects of the approved process. -/
def requiredCapabilities : ToolOp → List Capability.Access
  | .listFiles args => [.read (.tree args.path)]
  | .readFile args => [.read (.exact args.path)]
  | .searchFiles args => [.read (.tree args.path)]
  | .editFile args => [.read (.exact args.path), .write (.exact args.path)]
  | .createFile args => [.write (.exact args.path)]
  | .runProcess args => [.process args.argv args.cwd]
  | .readArtifact args => [.artifact args.id]

def policy (config : Config) (operation : ToolOp) : Decision :=
  match operation with
  | .runProcess _ => match config.commands with
    | .allow => .allow | .deny => .deny | .ask => .ask
  | _ => .allow

def application : Application where
  id := "coding"
  version := 1
  Operation := ToolOp
  operationRepr := inferInstance
  operationDecEq := inferInstance
  operationToJson := inferInstance
  operationFromJson := inferInstance
  Result := fun _ => ToolResult
  resultToJson := fun _ => inferInstance
  resultFromJson := fun _ => inferInstance
  Witness := EditWitness
  witnessRepr := inferInstance
  witnessToJson := inferInstance
  witnessFromJson := inferInstance
  Resolution := Resolution
  resolutionToJson := inferInstance
  resolutionFromJson := inferInstance
  defaultInstructions := "You are a coding agent. Inspect files before editing; run relevant tests; explain your result."
  schemas := toolSchemas
  decode := decodeOperation
  name := ToolOp.name
  args := ToolOp.args
  requiredCapabilities := requiredCapabilities
  policy := policy
  render := fun _ result => result
  artifactRead := fun | .readArtifact args => some args.id | _ => none
  settledTimeout := fun config operation => config.executionProfile == .bubblewrap &&
    match operation with | .runProcess _ => true | _ => false
  readOnly := fun
    | .listFiles _ | .readFile _ | .searchFiles _ | .readArtifact _ => true
    | _ => false
  mayAbandon := fun | .editFile _ | .createFile _ => true | _ => false
  validateWitness := validateWitness
  resolve := resolve
  operatorResolution := fun | .editPostimage _ => false | _ => true

end Harness.Coding

namespace Harness

/-- Existing coding callers retain their default, while the engine uses `Call app`. -/
abbrev ToolCall (app : Application := Coding.application) := Call app

namespace Recovery
abbrev EditWitness := Coding.EditWitness
abbrev Resolution := Coding.Resolution
namespace Resolution
abbrev editPostimage := Coding.Resolution.editPostimage
abbrev processCompleted := Coding.Resolution.processCompleted
abbrev processAbandoned := Coding.Resolution.processAbandoned
end Resolution
end Recovery
end Harness
