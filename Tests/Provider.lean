import Harness.Adapter.Provider
import Harness.Applications.Coding.Schemas
import Harness.Core.Transition

namespace Tests.Provider
open Lean Harness Harness.Provider

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError s!"provider test failed: {label}"

private def response (content : Array Json) (stop : String := "end_turn") : Json :=
  Json.mkObj [("type", toJson "message"), ("role", toJson "assistant"),
    ("content", toJson content), ("stop_reason", toJson stop),
    ("usage", Json.mkObj [("input_tokens", toJson (12 : Nat)), ("output_tokens", toJson (7 : Nat))])]

private def textBlock (text : String) : Json :=
  Json.mkObj [("type", toJson "text"), ("text", toJson text)]

private def callBlock : Json := Json.mkObj [("type", toJson "tool_use"),
  ("id", toJson "call-1"), ("name", toJson "read"),
  ("input", Json.mkObj [("path", toJson "README.md")])]

private def isMalformed : ModelObservation → Bool
  | .failure .malformed _ => true
  | _ => false

private def admitted : State :=
  admitModel (init "provider-contract" { model := "configured-model", workspace := "/tmp/workspace" }
    "inspect the repository")

/-- Feed the provider result to the continuation used by the running harness. -/
private def receive (json : Json) : IO State :=
  match step admitted with
  | ⟨.model _, continuation⟩ => pure (continuation (normalizeResponse json))
  | _ => throw (IO.userError "provider contract did not reach model inference")

/-- Execute one admitted read through the sequential control/tool continuations. -/
private def completeRead (s : State) : IO State := do
  let ready ← match step s with
    | ⟨.control, continuation⟩ => pure (continuation {})
    | _ => throw (IO.userError "provider contract expected tool control")
  match step ready with
  | ⟨.tool call, continuation⟩ =>
    match call.operation with
    | .readFile _ => pure (continuation (.success { text := "file contents" }))
    | _ => throw (IO.userError "provider contract expected read tool")
  | _ => throw (IO.userError "provider contract expected admitted tool")

private def stoppedFailure (s : State) : Bool :=
  match s.phase with
  | .stopped (.failure _) => true
  | _ => false

/-- Provider contract fixtures, independent of real credentials and the network. -/
def run : IO Unit := do
  let final := normalizeResponse (response #[textBlock "finished"])
  check "complete answer and usage" <| match final with
    | .success r => r.text == "finished" && r.stop == .endTurn && r.calls.isEmpty &&
      r.usage.any (fun u => u.inputTokens == 12 && u.outputTokens == 7)
    | _ => false
  let use := normalizeResponse (response #[textBlock "reading", callBlock] "tool_use")
  check "client call normalized" <| match use with
    | .success r => r.stop == .toolUse && r.calls.length == 1 &&
      r.calls.any (fun c => c.id == "call-1" && c.name == "read")
    | _ => false
  let broken := Json.mkObj [("type", toJson "tool_use"), ("input", toJson "partial")]
  check "malformed later call rejects complete response" <|
    isMalformed (normalizeResponse (response #[callBlock, broken] "tool_use"))
  check "truncation admits no apparent complete call" <|
    match normalizeResponse (response #[callBlock, broken] "max_tokens") with
    | .success r => r.stop == .maxTokens && r.calls.isEmpty
    | _ => false
  check "context-window stop admits no call" <|
    match normalizeResponse (response #[callBlock] "model_context_window_exceeded") with
    | .success r => r.stop == .contextOverflow && r.calls.isEmpty
    | _ => false
  check "end-turn call mismatch rejected" <|
    isMalformed (normalizeResponse (response #[callBlock]))
  check "empty tool-use rejected" <|
    isMalformed (normalizeResponse (response #[textBlock "waiting"] "tool_use"))
  check "server tools unsupported explicitly" <|
    isMalformed (normalizeResponse (response #[Json.mkObj [("type", toJson "server_tool_use")]]))
  check "unknown stop is non-success stop" <|
    match normalizeResponse (response #[textBlock "paused"] "pause_turn") with
    | .success r => r.stop == .other
    | _ => false
  check "partial JSON rejected" <| isMalformed (normalizeHttp 200 "{\"content\":[")
  check "authentication classified" <| match normalizeHttp 401 "secret-like remote body" with
    | .failure .authentication _ => true
    | _ => false
  check "rate limit classified" <| match normalizeHttp 429 "{}" with
    | .failure .rateLimit _ => true
    | _ => false
  check "transient server failure classified" <| match normalizeHttp 529 "{}" with
    | .failure .transport _ => true
    | _ => false
  let thinking := Json.mkObj [("type", toJson "thinking"), ("thinking", toJson "opaque"),
    ("signature", toJson "opaque-signature")]
  let content := #[thinking, textBlock "done"]
  check "reasoning signatures retained" <| match normalizeResponse (response content) with
    | .success r => r.content == content
    | _ => false
  let request : ModelRequest := { model := "configured-model", system := "frozen instructions", messages := [{ role := "assistant", content := content }], maxTokens := 42, tools := Coding.toolSchemas }
  let encoded := encodeRequest request
  let summary := encodeRequest {request with purpose := .summary}
  check "summary transport omits tools and tool choice" <|
    (summary.getObjVal? "tools").toOption.isNone && (summary.getObjVal? "tool_choice").toOption.isNone &&
    (summary.getObjValAs? String "system").toOption == some request.system &&
    (summary.getObjVal? "messages").toOption == some (toJson request.messages)
  check "request preserves content blocks" <|
    match encoded.getObjVal? "messages" with
    | .ok value => value == toJson request.messages
    | .error _ => false
  check "registry includes retained-artifact retrieval" (Coding.toolSchemas.size == 7 &&
    Coding.toolSchemas.any (fun schema => (schema.getObjValAs? String "name").toOption == some "artifact"))
  check "task transports exactly its recorded schemas" <|
    (encoded.getObjVal? "tools").toOption == some (toJson request.tools)
  check "empty registry does not silently advertise coding tools" <|
    ((encodeRequest {request with tools := #[]}).getObjVal? "tools").toOption.isNone
  let domainSchemas := #[Json.mkObj [("name", toJson "warehouse_totals")]]
  check "application schemas replace the coding registry" <|
    ((encodeRequest {request with tools := domainSchemas}).getObjVal? "tools").toOption ==
      some (toJson domainSchemas)
  let rawUsage := Json.mkObj [("input_tokens", toJson (12 : Nat)),
    ("output_tokens", toJson (7 : Nat)), ("cache_read_input_tokens", toJson (123 : Nat))]
  let withCache := Json.mkObj [("type", toJson "message"), ("role", toJson "assistant"),
    ("content", toJson #[textBlock "done"]), ("stop_reason", toJson "end_turn"),
    ("usage", rawUsage)]
  check "all provider usage fields retained" <| match normalizeResponse withCache with
    | .success r => r.usage.any (fun u => u.raw == rawUsage)
    | _ => false
  let withoutUsage := Json.mkObj [("type", toJson "message"), ("role", toJson "assistant"),
    ("content", toJson #[textBlock "done"]), ("stop_reason", toJson "end_turn")]
  check "missing usage remains unknown" <| match normalizeResponse withoutUsage with
    | .success r => r.usage.isNone
    | _ => false
  check "refusal is preserved" <| match normalizeResponse (response #[textBlock "declined"] "refusal") with
    | .success r => r.stop == .refusal
    | _ => false

  let redacted := Json.mkObj [("type", toJson "redacted_thinking"),
    ("data", toJson "opaque-redacted-data")]
  let finalContent := #[thinking, textBlock "first ", redacted, textBlock "second"]
  let finished ← receive (response finalContent)
  check "normalized text accepted with exact opaque history and known usage" <|
    (match finished.phase with | .stopped (.final answer) => answer == "first second" | _ => false) &&
    toJson finished.history == toJson (admitted.history ++ [{ role := "assistant", content := finalContent }]) &&
    finished.knownInputTokens == 12 && finished.knownOutputTokens == 7 && finished.unknownUsage == 0

  let secondCall := Json.mkObj [("type", toJson "tool_use"), ("id", toJson "call-2"),
    ("name", toJson "read"), ("input", Json.mkObj [("path", toJson "main.lean")])]
  let batchContent := #[thinking, textBlock "read both", callBlock, redacted, secondCall]
  let accepted ← receive (response batchContent "tool_use")
  check "normalized batch accepted in content order with exact opaque history" <|
    (match accepted.phase with
    | .controlTools calls => calls.map (·.id) == ["call-1", "call-2"]
    | _ => false) && accepted.seenCallIds == ["call-1", "call-2"] &&
    toJson accepted.history == toJson (admitted.history ++ [{ role := "assistant", content := batchContent }])
  let completed ← completeRead (← completeRead accepted)
  let nextControl := consumeControl completed (some []) {}
  let nextModel := consumeControl nextControl none {}
  let nextRequest := encodeRequest (modelRequest nextModel)
  check "normalized tool batch completes and survives the next request" <|
    completed.toolDispatches == 2 && nextModel.modelAttempts == 2 &&
    (match nextRequest.getObjVal? "messages" with
    | .ok messages => messages == toJson (completed.history ++ [budgetMessage nextModel])
    | .error _ => false) &&
    (match completed.history.reverse with
    | results :: assistant :: _ => assistant.content == batchContent && results.role == "user" &&
      results.content.size == 2 &&
      ((results.content[0]!).getObjValAs? String "tool_use_id").toOption == some "call-1" &&
      ((results.content[1]!).getObjValAs? String "tool_use_id").toOption == some "call-2"
    | _ => false)

  let invalidArgs := Json.mkObj [("type", toJson "tool_use"), ("id", toJson "call-2"),
    ("name", toJson "read"), ("input", Json.mkObj [("path", toJson "../escape")])]
  let rejectedBatch ← receive (response #[callBlock, invalidArgs] "tool_use")
  check "provider-valid later arguments reject the whole batch in core" <|
    (match rejectedBatch.phase with | .controlModel => true | _ => false) && rejectedBatch.toolDispatches == 0 && rejectedBatch.seenCallIds.isEmpty &&
    toJson rejectedBatch.history == toJson (admitted.history ++ [responseRepairMessage .invalidBatch]) && rejectedBatch.knownInputTokens == 12
  let malformed ← receive (response #[callBlock, broken] "tool_use")
  check "malformed adapter response preserves unknown-usage accounting" <|
    (match malformed.phase with | .controlModel => true | _ => false) && malformed.unknownUsage == 1 && malformed.knownInputTokens == 0 &&
    malformed.toolDispatches == 0 && toJson malformed.history == toJson (admitted.history ++ [responseRepairMessage .malformed])
  let truncated ← receive (response #[callBlock, broken] "max_tokens")
  check "truncated adapter response consumes known usage without admitting content" <|
    (match truncated.phase with | .controlModel => true | _ => false) && truncated.knownInputTokens == 12 && truncated.knownOutputTokens == 7 &&
    truncated.unknownUsage == 0 && truncated.toolDispatches == 0 &&
    toJson truncated.history == toJson (admitted.history ++ [responseRepairMessage .truncated])
  let overflow ← receive (response #[callBlock, broken] "model_context_window_exceeded")
  check "context overflow remains a limit without parsing incomplete blocks" <|
    (match overflow.phase with | .stopped (.limit _) => true | _ => false) &&
    overflow.knownInputTokens == 12 && overflow.toolDispatches == 0 &&
    toJson overflow.history == toJson admitted.history
  for reason in ["refusal", "pause_turn"] do
    let rejected ← receive (response #[callBlock] reason)
    check s!"{reason} cannot admit apparently complete tool calls" <|
      stoppedFailure rejected && rejected.toolDispatches == 0 && rejected.seenCallIds.isEmpty &&
      toJson rejected.history == toJson admitted.history && rejected.knownInputTokens == 12
  IO.println "provider: 29 contract checks passed (including normalization through core continuations)"

end Tests.Provider
