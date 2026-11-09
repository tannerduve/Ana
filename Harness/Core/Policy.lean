import Harness.Core.Protocol

namespace Harness
open Lean

/-- Lexical guard only. The filesystem adapter also rejects symlinks. -/
def safePath (p : String) : Bool :=
  !p.isEmpty && !p.startsWith "/" && !(p.splitOn "/").contains ".." &&
    !(p.toList.contains '\x00')

def decodeCall (raw : RawCall) : Except String ToolCall := do
  if raw.id.isEmpty then throw "empty tool call identity"
  let allowed := match raw.name with
    | "list" => ["path", "limit"]
    | "read" => ["path", "startLine", "endLine"]
    | "search" => ["query", "path", "limit", "caseSensitive"]
    | "edit" => ["path", "old", "new", "expectedSha256"]
    | "create" => ["path", "content", "overwrite"]
    | "process" => ["argv", "cwd"]
    | _ => []
  let fields ← raw.input.getObj?
  if fields.toList.any (fun (k, _) => !allowed.contains k) then throw "unknown tool argument"
  let defaults : List (String × Json) := match raw.name with
    | "list" => [("path", toJson "."), ("limit", toJson (200 : Nat))]
    | "read" => [("startLine", toJson (1 : Nat)), ("endLine", toJson (200 : Nat))]
    | "search" => [("path", toJson "."), ("limit", toJson (100 : Nat)), ("caseSensitive", toJson true)]
    | "create" => [("overwrite", toJson false)]
    | "process" => [("cwd", toJson ".")]
    | _ => []
  let input := Json.mkObj (defaults ++ fields.toList)
  let op ← match raw.name with
    | "list" => ToolOp.listFiles <$> fromJson? input
    | "read" => ToolOp.readFile <$> fromJson? input
    | "search" => ToolOp.searchFiles <$> fromJson? input
    | "edit" => ToolOp.editFile <$> fromJson? input
    | "create" => ToolOp.createFile <$> fromJson? input
    | "process" => ToolOp.runProcess <$> fromJson? input
    | _ => throw s!"unknown tool: {raw.name}"
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
    if (raw.input.getObjVal? "env").isOk then throw "custom process environment is unsupported"
  return ⟨raw.id, op⟩

/-- Validate the entire batch before accepting any assistant tool-use message. -/
def validateBatch (cfg : Config) (seen : List String) (calls : List RawCall) : Except String (List ToolCall) := do
  if calls.isEmpty then throw "tool-use response contained no calls"
  if calls.length > cfg.maxBatchCalls then throw "tool batch limit exceeded"
  let (_, result) ← calls.foldlM (init := (seen, [])) fun (ids, acc) raw => do
    if ids.contains raw.id then throw "duplicate tool call identity"
    let call ← decodeCall raw
    return (raw.id :: ids, acc ++ [call])
  return result

inductive Decision where
  | allow | deny | ask
  deriving Repr, BEq, DecidableEq

def policy (cfg : Config) (call : ToolCall) : Decision :=
  match call.operation with
  | .runProcess _ => match cfg.commands with
    | .allow => .allow
    | .deny => .deny
    | .ask => .ask
  | _ => .allow

/-- Grants bind to the entire typed call, including its identity and arguments. -/
def authorized (cfg : Config) (grant : Option ToolCall) (call : ToolCall) : Bool :=
  decide (policy cfg call = .allow) || (decide (policy cfg call = .ask) && decide (grant = some call))

end Harness
