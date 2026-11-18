import Harness.Adapter.Provider
import Harness.Adapter.ProcessIO

/-!
Official CLI inference adapters. Each invocation receives the complete harness-owned context
and returns proposals in a small JSON envelope. Application effects still pass through the
existing decoder, admission, journal and tool interpreter. CLI authentication remains in the
official executable; this module never reads credentials. Native CLI processes are trusted
adapters, not part of the proved core. One reserved attempt counts one CLI invocation, which
may contain upstream retries or structured-output requests.
-/
namespace Harness.CLIProvider
open Lean

def instructions : String :=
  "You are the inference backend of a separate agent harness. Do not use native tools, inspect " ++
  "your working directory, or execute actions yourself. The JSON on stdin contains the actual " ++
  "application system instructions, conversation, offered tool schemas, purpose and output " ++
  "allowance. Follow that application conversation. Return exactly one JSON object with text " ++
  "and calls. text is a string. calls is an array of objects with exactly id, name, and " ++
  "input_json (a string encoding the tool's JSON argument object). Propose only offered tools, " ++
  "using unique call ids never used in the supplied history. The host executes proposals and " ++
  "sends their observations in the next invocation. Your native CLI sandbox is separate from " ++
  "the host application's tools: a read-only native CLI can still propose host edit/create " ++
  "operations. Infer host permissions only from the supplied application conversation and " ++
  "tool observations. Do not claim the host workspace is read-only because your native CLI is. " ++
  "An action is not completed until the supplied history contains its tool result. " ++
  "To finish, return the final answer as text " ++
  "and an empty calls array. For a summary request, summarize the supplied conversation with " ++
  "no tool calls. Keep output within the supplied allowance. Do not wrap JSON in Markdown."

/-- input_json keeps the transport schema independent of an application's argument types.
The real application decoder still validates the parsed arguments before admission. -/
def outputSchema : Json :=
  let string := Json.mkObj [("type", toJson "string")]
  let call := Json.mkObj [("type", toJson "object"),
    ("properties", Json.mkObj [("id", string), ("name", string), ("input_json", string)]),
    ("required", toJson #["id", "name", "input_json"]), ("additionalProperties", toJson false)]
  Json.mkObj [("type", toJson "object"),
    ("properties", Json.mkObj [("text", string),
      ("calls", Json.mkObj [("type", toJson "array"), ("items", call)])]),
    ("required", toJson #["text", "calls"]), ("additionalProperties", toJson false)]

private def exactFields (value : Json) (names : List String) : Except String Unit := do
  let fields ← value.getObj?
  unless fields.size == names.length && fields.toList.all (fun pair => names.contains pair.1) do
    throw "unexpected CLI response fields"

def decodeProposal (value : Json) (usage : Option Usage) : Except String ModelResponse := do
  exactFields value ["text", "calls"]
  let text ← value.getObjValAs? String "text"
  let calls ← (← value.getObjVal? "calls").getArr?
  unless calls.size ≤ 32 do throw "CLI response exceeds 32 proposed calls"
  let mut content := if text.isEmpty then #[] else
    #[Json.mkObj [("type", toJson "text"), ("text", toJson text)]]
  let mut decoded : List RawCall := []
  let mut work := 0
  for call in calls do
    exactFields call ["id", "name", "input_json"]
    let id ← call.getObjValAs? String "id"
    let name ← call.getObjValAs? String "name"
    let inputText ← call.getObjValAs? String "input_json"
    let (input, spent) ← JsonBounds.parseWithWork inputText work
    work := spent
    let _ ← input.getObj?
    unless !id.isEmpty && !name.isEmpty do throw "empty CLI call identity"
    decoded := decoded ++ [{id, name, input}]
    content := content.push <| Json.mkObj [("type", toJson "tool_use"),
      ("id", toJson id), ("name", toJson name), ("input", input)]
  return {
    content, calls := decoded, text
    stop := if decoded.isEmpty then .endTurn else .toolUse
    usage }

private def claudeUsage (value : Json) : Option Usage := do
  let raw ← (value.getObjVal? "usage").toOption
  let input ← (raw.getObjValAs? Nat "input_tokens").toOption
  let output ← (raw.getObjValAs? Nat "output_tokens").toOption
  let cacheRead := (raw.getObjValAs? Nat "cache_read_input_tokens").toOption.getD 0
  let cacheWrite := (raw.getObjValAs? Nat "cache_creation_input_tokens").toOption.getD 0
  return {
    inputTokens := input + cacheRead + cacheWrite, outputTokens := output
    raw := Json.mkObj [("input_tokens", toJson input), ("output_tokens", toJson output),
      ("cache_read_input_tokens", toJson cacheRead), ("cache_creation_input_tokens", toJson cacheWrite)]}

private def codexUsage (value : Json) : Option Usage := do
  let raw ← (value.getObjVal? "usage").toOption
  let input ← (raw.getObjValAs? Nat "input_tokens").toOption
  let output ← (raw.getObjValAs? Nat "output_tokens").toOption
  let cached := (raw.getObjValAs? Nat "cached_input_tokens").toOption.getD 0
  if cached > input then none else
    some {
      inputTokens := input, outputTokens := output
      raw := Json.mkObj [("input_tokens", toJson input), ("output_tokens", toJson output),
        ("cached_input_tokens", toJson cached)]}

private def malformed : ModelObservation := .failure .malformed "CLI returned an invalid or incomplete inference response"

def normalizeClaude (body : String) : ModelObservation :=
  match decode body with
  | .ok response => .success response
  | .error _ => malformed
where
  decode (body : String) : Except String ModelResponse := do
    let value ← JsonBounds.parse body
    unless (← value.getObjValAs? String "type") == "result" &&
        (← value.getObjValAs? String "subtype") == "success" &&
        !(← value.getObjValAs? Bool "is_error") do
      throw "unsuccessful Claude Code result"
    let proposal ← match value.getObjVal? "structured_output" with
      | .ok output =>
        if output.isNull then JsonBounds.parse (← value.getObjValAs? String "result") else pure output
      | .error _ => JsonBounds.parse (← value.getObjValAs? String "result")
    decodeProposal proposal (claudeUsage value)

/-- Only a single completed turn containing reasoning and one final agent message is admitted.
Native tool events, error events, repeated terminals and incomplete streams authorize no tools. -/
def normalizeCodex (body : String) : ModelObservation :=
  match decode body with
  | .ok response => .success response
  | .error _ => malformed
where
  decode (body : String) : Except String ModelResponse := do
    let mut started := false
    let mut turn := false
    let mut completed := false
    let mut message : Option String := none
    let mut usage : Option Usage := none
    let mut work := 0
    for line in body.splitOn "\n" do
      if line.trimAscii.toString.isEmpty then continue
      if completed then throw "event after completed Codex turn"
      let (event, spent) ← JsonBounds.parseWithWork line work
      work := spent
      match ← event.getObjValAs? String "type" with
      | "thread.started" =>
        if started then throw "repeated Codex thread"
        let id ← event.getObjValAs? String "thread_id"
        unless !id.isEmpty do throw "missing Codex thread identity"
        started := true
      | "turn.started" =>
        unless started && !turn do throw "invalid Codex turn start"
        turn := true
      | "item.started" | "item.updated" | "item.completed" =>
        let item ← event.getObjVal? "item"
        match ← item.getObjValAs? String "type" with
        | "error" =>
          -- Codex can report unavailable optional features between thread startup and
          -- turn startup. It must still produce a complete successful inference turn.
          unless started && !turn do throw "Codex error during inference"
        | "reasoning" => unless turn do throw "Codex reasoning outside turn"
        | "agent_message" =>
          unless turn do throw "Codex message outside turn"
          if (← event.getObjValAs? String "type") == "item.completed" then
            if message.isSome then throw "multiple Codex agent messages"
            message := some (← item.getObjValAs? String "text")
        | _ => throw "native Codex tool activity is not an inference response"
      | "turn.completed" =>
        unless turn && message.isSome do throw "incomplete Codex turn"
        usage := codexUsage event
        completed := true
      | _ => throw "unexpected Codex event"
    unless completed do throw "Codex turn did not complete"
    let some text := message | throw "Codex final message missing"
    decodeProposal (← JsonBounds.parse text) usage

private def environment : IO (Array (String × Option String)) := do
  -- API keys, provider overrides, hooks, Node preload options and proxy settings are not inherited.
  -- Auth files/keychains are accessed only by the official CLIs through their normal login flow.
  let mut result := #[]
  for key in #["HOME", "PATH", "LANG", "LC_ALL", "TMPDIR", "XDG_CONFIG_HOME", "XDG_DATA_HOME",
      "XDG_CACHE_HOME", "XDG_STATE_HOME", "CODEX_HOME", "CLAUDE_CONFIG_DIR", "SSL_CERT_FILE", "SSL_CERT_DIR"] do
    if let some value ← IO.getEnv key then result := result.push (key, some value)
  return result.push ("CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC", some "1")

private def contained (root : String) (path : System.FilePath) : IO Bool := do
  if root.isEmpty then return false
  return (← IO.FS.realPath root).components.isPrefixOf path.components

private def executable (backend : ModelBackend) (workspace session : String) : IO String := do
  let name := if backend == .claudeCode then "claude" else "codex"
  let path := (← IO.getEnv "PATH").getD "/usr/bin:/bin"
  for entry in path.splitOn ":" do
    -- Resolve only absolute, operator-installed PATH entries. A model-writable CLI
    -- would turn an otherwise permitted edit into credential-bearing code execution.
    if !(System.FilePath.mk entry).isAbsolute then continue
    let candidate := System.FilePath.mk entry / name
    if !(← candidate.pathExists) then continue
    let resolved ← IO.FS.realPath candidate
    unless (← resolved.metadata).type == .file do continue
    if (← contained workspace resolved) || (← contained session resolved) then
      throw <| IO.userError "CLI executable must be outside the application workspace and session"
    return resolved.toString
  throw <| IO.userError "CLI executable is not installed on an absolute PATH"

def arguments (backend : ModelBackend) (model : String) (schema : System.FilePath) : Array String :=
  let selection := if model == "default" then #[] else #["--model", model]
  match backend with
  | .claudeCode => #["--print", "--output-format", "json", "--tools", "",
      "--allowedTools", "StructuredOutput", "--strict-mcp-config", "--mcp-config", "{\"mcpServers\":{}}",
      "--safe-mode", "--setting-sources", "", "--no-session-persistence", "--no-chrome",
      "--disable-slash-commands", "--permission-mode", "dontAsk", "--permission-prompts", "none",
      "--system-prompt", instructions, "--json-schema", outputSchema.compress] ++ selection
  | .codex => #["exec", "--json", "--ephemeral", "--ignore-user-config", "--ignore-rules",
      "--skip-git-repo-check", "--sandbox", "read-only", "--color", "never",
      "--output-schema", schema.toString,
      "-c", "approval_policy=\"never\"", "-c", "forced_login_method=\"chatgpt\"",
      "-c", "model_provider=\"openai\"", "-c", "web_search=\"disabled\"",
      "-c", "mcp_servers={}", "-c", "project_doc_max_bytes=0",
      "-c", "notify=[]", "-c", "tools.update_plan.enabled=false",
      "-c", "include_permissions_instructions=false", "-c", "include_collaboration_mode_instructions=false",
      "-c", "model_instructions_file=" ++
        (toJson ((schema.parent.getD ".") / "inference-instructions.txt").toString).compress] ++
      (#["shell_tool", "unified_exec", "shell_snapshot", "hooks", "apps", "plugins", "multi_agent",
        "multi_agent_v2", "code_mode", "code_mode_host", "browser_use", "computer_use",
        "image_generation", "view_image", "goals", "sleep_tool", "skill_search",
        "skill_mcp_dependency_install"].foldl (fun args feature => args ++ #["--disable", feature]) #[]) ++
      selection ++ #["-"]
  | .anthropic => #[]

def request (backend : ModelBackend) (model : ModelRequest) (timeoutMs : Nat)
    (deadline : Option Nat) (cancelPath : String) (responseBytes : Nat)
    (workspace : String := "") (session : String := "") : IO ModelObservation := do
  if backend == .anthropic then return .failure .invalidRequest "CLI backend required"
  let started ← IO.monoMsNow
  if timeoutMs == 0 || responseBytes == 0 || responseBytes > 16 * 1024 * 1024 then
    return .failure .invalidRequest "invalid CLI response or timeout bound"
  let payload := (Json.mkObj [("instructions", toJson instructions), ("request", toJson model)]).compress
  if payload.utf8ByteSize > 8 * 1024 * 1024 then
    return .failure .invalidRequest "CLI request exceeds 8 MiB"
  let command ← try executable backend workspace session catch _ =>
    return .failure .invalidRequest
      "CLI executable unavailable or inside the application workspace; install it on an absolute PATH outside the workspace"
  try
    IO.FS.withTempDir fun directory => do
      -- Never run the native CLI in the application workspace or session/journal directory.
      let canonical ← IO.FS.realPath directory
      if (← contained workspace canonical) || (← contained session canonical) then
        return .failure .invalidRequest "CLI scratch directory must be outside the application workspace and session; change TMPDIR"
      let schema := directory / "response-schema.json"
      IO.FS.writeFile schema outputSchema.compress
      IO.FS.writeFile (directory / "inference-instructions.txt") instructions
      let result ← ProcessIO.capture {
        cmd := command
        args := arguments backend model.model schema
        cwd := some directory
        input := payload.toUTF8
        timeoutMs, startedMs := some started, invocationDeadlineMs := deadline
        cancelPath, stdoutBytes := responseBytes, stderrBytes := 4096
        environment := some (← environment) }
      match result.status with
      | .failedToStart =>
        return .failure .invalidRequest (if backend == .claudeCode then
          "Claude Code could not start; install claude and run claude auth login"
          else "Codex could not start; install codex and run codex login")
      | .interrupted => return .interrupted
      | .uncertain | .timedOut => return .uncertain "CLI invocation did not settle; usage unknown"
      | .completed =>
        if result.exitCode != some 0 then
          return .failure .invalidRequest "CLI invocation failed; check CLI login, model access, and version outside the harness"
        if result.stdoutTotal > responseBytes then
          return .failure .malformed "CLI output exceeded response byte allowance; no proposals admitted"
        let some body := String.fromUTF8? result.stdout | return malformed
        return if backend == .claudeCode then normalizeClaude body else normalizeCodex body
  catch _ => return .uncertain "CLI adapter failed; usage unknown"

end Harness.CLIProvider
