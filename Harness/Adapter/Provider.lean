import Harness.Core.ModelResponse
import Harness.Adapter.JsonBounds

/-!
Pure Anthropic Messages encoding and complete-response normalization.
No transport, prompting, tool execution, retry, or permission decisions occur here.
The caller passes only a complete, bounded HTTP response body.
-/
namespace Harness.Provider
open Lean


/-- Encode normalized history without flattening or reconstructing opaque blocks. -/
def encodeRequest (request : ModelRequest) (stream : Bool := false) : Json :=
  let body := Json.mkObj [("model", toJson request.model), ("system", toJson request.system),
    ("max_tokens", toJson request.maxTokens), ("messages", toJson request.messages),
    ("stream", toJson stream)]
  match request.purpose with
  | .task => if request.tools.isEmpty then body else
      body.mergeObj (Json.mkObj [("tools", toJson request.tools)])
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
    match JsonBounds.parse body with
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
