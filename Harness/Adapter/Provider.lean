import Harness.Core.ModelResponse

/-!
Pure Anthropic Messages encoding and complete-response normalization.
No transport, prompting, tool execution, retry, or permission decisions occur here.
The caller passes only a complete, bounded HTTP response body.
-/
namespace Harness.Provider
open Lean

private def property (kind description : String) : Json :=
  Json.mkObj [("type", toJson kind), ("description", toJson description)]

private def tool (name description : String) (fields : List (String × Json))
    (required : List String) : Json :=
  Json.mkObj [("name", toJson name), ("description", toJson description),
    ("input_schema", Json.mkObj [("type", toJson "object"),
      ("properties", Json.mkObj fields), ("required", toJson required),
      ("additionalProperties", toJson false)])]

/-- The static coding registry. Schemas match the core decoder and IO adapters. -/
def toolSchemas : Array Json := #[
  tool "list"
    "List workspace files recursively in stable sorted traversal order. Paths are relative to the workspace; symlinks and parent traversal are rejected. Results are bounded by limit; ignored metadata directories are omitted. Inspect a subdirectory by calling list again with its path."
    [("path", property "string" "Workspace-relative directory, default '.'"),
     ("limit", property "integer" "Maximum entries, default 200")]
    [],
  tool "read"
    "Read a UTF-8 file with 1-based inclusive line bounds. The result includes the SHA256 identity of the full file; use it as expectedSha256 in a subsequent edit. Outputs are bounded and truncation is explicit. Read a later line range to retrieve omitted content."
    [("path", property "string" "Workspace-relative file path"),
     ("startLine", property "integer" "First line, default 1"),
     ("endLine", property "integer" "Last line, default 200")]
    ["path"],
  tool "search"
    "Search UTF-8 workspace files for a literal substring. Results contain paths and line numbers in stable order. Searches skip symlinks and ignored metadata directories, and stop at the configured match limit. Narrow the path or query if results are truncated."
    [("query", property "string" "Literal nonempty search string"),
     ("path", property "string" "Workspace-relative file or directory, default '.'"),
     ("limit", property "integer" "Maximum matches, default 100"),
     ("caseSensitive", property "boolean" "Case-sensitive matching, default true; false ignores ASCII letter case only")]
    ["query"],
  tool "edit"
    "Replace one exact occurrence of old with new in a workspace UTF-8 file. Read the file first and supply the returned full-file SHA256 as expectedSha256. An absent or ambiguous match or changed preimage fails without writing. Refresh the file after a stale-preimage error; edits use atomic replacement under a single-writer assumption."
    [("path", property "string" "Workspace-relative file path"),
     ("old", property "string" "Exact nonempty text to replace, must occur once"),
     ("new", property "string" "Replacement text, may be empty"),
     ("expectedSha256", property "string" "64-character SHA256 from a prior read")]
    ["path", "old", "new", "expectedSha256"],
  tool "create"
    "Create a UTF-8 file in the workspace. Existing files fail unless overwrite is explicitly true. Parent directories must already exist and may not be symlinks. Prefer edit with a preimage identity for changes to existing files."
    [("path", property "string" "Workspace-relative file path"),
     ("content", property "string" "Complete new file content"),
     ("overwrite", property "boolean" "Permit replacing an existing file, default false")]
    ["path", "content"],
  tool "process"
    "Run a program using an argument array without implicit shell expansion. Commands may require exact-action human approval. The current directory is workspace-relative, but process access is governed by the operating system and is not sandboxed. Runtime deadlines and output limits apply; a nonzero exit is a completed command result, and timeout may leave side effects."
    [("argv", Json.mkObj [("type", toJson "array"), ("items", property "string" "Argument"),
        ("minItems", toJson (1 : Nat)), ("description", toJson "Program followed by its arguments")]),
     ("cwd", property "string" "Workspace-relative working directory, default '.'")]
    ["argv"]]

/-- Encode normalized history without flattening or reconstructing opaque blocks. -/
def encodeRequest (request : ModelRequest) : Json :=
  let body := Json.mkObj [("model", toJson request.model), ("system", toJson request.system),
    ("max_tokens", toJson request.maxTokens), ("messages", toJson request.messages),
    ("stream", toJson false)]
  match request.purpose with
  | .task => body.mergeObj (Json.mkObj [("tools", toJson toolSchemas)])
  | .summary => body

private def fieldString (json : Json) (key : String) : Except String String := do
  (← json.getObjVal? key).getStr?

private def parseUsage (json : Json) : Option Usage := do
  let usage ← (json.getObjVal? "usage").toOption
  let input ← ((usage.getObjVal? "input_tokens").bind Json.getNat?).toOption
  let output ← ((usage.getObjVal? "output_tokens").bind Json.getNat?).toOption
  return { inputTokens := input, outputTokens := output, raw := usage }

private def parseResponse (json : Json) : Except String ModelResponse := do
  unless (← fieldString json "type") == "message" do
    throw "expected complete message response"
  unless (← fieldString json "role") == "assistant" do
    throw "expected assistant response"
  let stop ← fieldString json "stop_reason"
  let content ← (← json.getObjVal? "content").getArr?
  -- A truncated response may contain malformed blocks. Do not parse or admit any
  -- apparent calls from it, but retain the original blocks for local diagnosis.
  if stop == "max_tokens" || stop == "model_context_window_exceeded" then
    return { content, calls := [], text := "", stop := if stop == "max_tokens" then .maxTokens else .contextOverflow, usage := parseUsage json }
  let (calls, text) ← parseModelContent content
  let reason := match stop with
    | "end_turn" => StopReason.endTurn
    | "tool_use" => StopReason.toolUse
    | "refusal" => StopReason.refusal
    | _ => StopReason.other
  if reason == .endTurn && !calls.isEmpty then
    throw "end_turn response contains tool calls"
  if reason == .toolUse && calls.isEmpty then
    throw "tool_use response contains no client tool calls"
  return { content, calls, text, stop := reason, usage := parseUsage json }

/-- Normalize one complete provider body. Argument decoding and batch admission
remain core policy, so a malformed later call prevents the entire batch. -/
def normalizeResponse (json : Json) : ModelObservation :=
  match parseResponse json with
  | .ok response => .success response
  | .error message => .failure .malformed message

private def shortMessage (body : String) : String :=
  String.ofList (body.toList.take 2048)

/-- HTTP status classification is deterministic; the core decides whether to retry. -/
def normalizeHttp (status : Nat) (body : String) : ModelObservation :=
  if status == 200 then
    match Json.parse body with
    | .ok json => normalizeResponse json
    | .error message => .failure .malformed s!"invalid response JSON: {message}"
  else if status == 401 || status == 403 then
    .failure .authentication "provider authentication failed"
  else if status == 429 then
    .failure .rateLimit "provider rate limit"
  else if status == 408 || status >= 500 then
    .failure .transport s!"provider HTTP {status}"
  else if status == 400 || status == 413 || status == 422 then
    .failure .invalidRequest s!"provider HTTP {status}: {shortMessage body}"
  else
    .failure .other s!"provider HTTP {status}: {shortMessage body}"

end Harness.Provider
