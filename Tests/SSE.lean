import Harness.Adapter.SSE
import Harness.Core.Transition

namespace Tests.SSE
open Lean Harness

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"SSE test failed: {label}")

private def event (kind : String) (fields : List (String × Json) := []) : String :=
  "event: " ++ kind ++ "\ndata: " ++ (Json.mkObj (("type", toJson kind) :: fields)).compress ++ "\n\n"

private def start : String := event "message_start" [("message", Json.mkObj [
  ("type", toJson "message"), ("role", toJson "assistant"), ("id", toJson "message-1"),
  ("content", toJson (#[] : Array Json)), ("stop_reason", .null),
  ("usage", Json.mkObj [("input_tokens", toJson (12 : Nat)), ("output_tokens", toJson (0 : Nat)),
    ("cache_read_input_tokens", toJson (9 : Nat))])])]

private def block (index : Nat) (content : Json) : String :=
  event "content_block_start" [("index", toJson index), ("content_block", content)]

private def delta (index : Nat) (kind key value : String) : String :=
  event "content_block_delta" [("index", toJson index),
    ("delta", Json.mkObj [("type", toJson kind), (key, toJson value)])]

private def stopBlock (index : Nat) : String := event "content_block_stop" [("index", toJson index)]

private def terminalDelta (reason : String := "end_turn") : String :=
  event "message_delta" [("delta", Json.mkObj [("stop_reason", toJson reason), ("stop_sequence", .null)]),
    ("usage", Json.mkObj [("output_tokens", toJson (8 : Nat))])]

private def terminal (reason : String := "end_turn") : String :=
  terminalDelta reason ++ event "message_stop"

private def textStream : String := start ++ block 0 (Json.mkObj [("type", toJson "text"), ("text", toJson "")]) ++
  delta 0 "text_delta" "text" "λ🙂\n" ++ event "ping" ++ delta 0 "text_delta" "text" "done" ++ stopBlock 0 ++ terminal

private def decode (chunks : Array ByteArray) (maximum := 2000000) : Except String (Json × String) := do
  let mut state : Harness.SSE.State := {maximumBytes := maximum}
  let mut text := ""
  for chunk in chunks do
    let (next, provisional) ← Harness.SSE.feed state chunk
    state := next
    text := text ++ String.join provisional.toList
  return (← Harness.SSE.finish state, text)

private def fails (stream : String) : Bool := (decode #[stream.toUTF8]).toOption.isNone

private def toolStart : String := block 0 (Json.mkObj [("type", toJson "tool_use"),
  ("id", toJson "call-1"), ("name", toJson "read"), ("input", Json.mkObj [])])

/-- Independent event fixtures and exhaustive two-way byte splits exercise the
actual pure decoder, without sockets, credentials, or a model. -/
def run : IO Unit := do
  let (expected, text) ← IO.ofExcept (decode #[textStream.toUTF8])
  check "unicode text and provisional content" (text == "λ🙂\ndone")
  check "complete normalization" <| match Provider.normalizeResponse expected with
    | .success response => response.text == text && response.stop == .endTurn &&
      response.usage.any (fun u => u.inputTokens == 12 && u.outputTokens == 8 &&
        (u.raw.getObjValAs? Nat "cache_read_input_tokens").toOption == some 9)
    | _ => false
  let bytes := textStream.toUTF8
  for i in [:bytes.size + 1] do
    let result := decode #[bytes.extract 0 i, bytes.extract i bytes.size]
    check s!"all byte splits {i}" (result.toOption == some (expected, text))
  let singles := (List.range bytes.size).toArray.map (fun i => bytes.extract i (i+1))
  check "one byte chunks including UTF8" ((decode singles).toOption == some (expected, text))
  let crlf := textStream.replace "\n" "\r\n"
  check "CRLF frames" ((decode #[crlf.toUTF8]).toOption == some (expected, text))
  check "CR-only framing" ((decode #[(textStream.replace "\n" "\r").toUTF8]).toOption == some (expected, text))
  check "optional UTF8 BOM" ((decode #[((String.singleton (Char.ofNat 0xFEFF)) ++ textStream).toUTF8]).toOption == some (expected, text))
  check "exact byte ceiling" ((decode #[bytes] bytes.size).toOption == some (expected, text))
  check "byte ceiling exceeded" ((decode #[bytes] (bytes.size - 1)).toOption.isNone)
  let tools := start ++ toolStart ++ delta 0 "input_json_delta" "partial_json" "{\"path\":" ++
    delta 0 "input_json_delta" "partial_json" "\"README.md\"}" ++ stopBlock 0 ++ terminal "tool_use"
  let (toolMessage, provisional) ← IO.ofExcept (decode #[tools.toUTF8])
  check "tool arguments never provisional" provisional.isEmpty
  check "tool stream complete and normalized" <| match Provider.normalizeResponse toolMessage with
    | .success response => response.calls.length == 1 && response.stop == .toolUse &&
      response.calls.any (fun call => (call.input.getObjValAs? String "path").toOption == some "README.md")
    | _ => false
  let unfinished :=  start ++ toolStart ++ delta 0 "input_json_delta" "partial_json" "{\"path\":" ++ stopBlock 0
  check "incomplete arguments rejected on ordinary stop" (fails (unfinished ++ terminal "tool_use"))
  let (truncated, _) ← IO.ofExcept (decode #[(unfinished ++ terminal "max_tokens").toUTF8])
  check "truncation preserves stop and authorizes no call" <| match Provider.normalizeResponse truncated with
    | .success response => response.stop == .maxTokens && response.calls.isEmpty
    | _ => false
  -- Even a complete earlier mutation belongs to the same incomplete batch.
  -- Exercise the actual model continuation, not only the normalized call list.
  let completeMutation := block 0 (Json.mkObj [("type", toJson "tool_use"),
    ("id", toJson "must-not-run"), ("name", toJson "create"), ("input", Json.mkObj [])]) ++
    delta 0 "input_json_delta" "partial_json" "{\"path\":\"marker.txt\",\"content\":\"must not execute\"}" ++ stopBlock 0
  let openFinal := block 1 (Json.mkObj [("type", toJson "tool_use"),
    ("id", toJson "partial-call"), ("name", toJson "read"), ("input", Json.mkObj [])]) ++
    delta 1 "input_json_delta" "partial_json" "{\"path\":"
  let incompleteBatch := start ++ completeMutation ++ openFinal
  for reason in ["max_tokens", "model_context_window_exceeded"] do
    let stream := (incompleteBatch ++ terminal reason).toUTF8
    for chunkSize in [1, 7, stream.size] do
      let chunks := (List.range ((stream.size + chunkSize - 1) / chunkSize)).toArray.map fun i =>
        stream.extract (i * chunkSize) (min stream.size ((i + 1) * chunkSize))
      let (message, _) ← IO.ofExcept (decode chunks)
      let .success response := Provider.normalizeResponse message
        | throw (IO.userError "terminal limit was not normalized")
      check "open limit discards all content with known usage" <|
        response.calls.isEmpty && response.content.isEmpty && response.text.isEmpty &&
        response.usage.any (fun u => u.inputTokens == 12 && u.outputTokens == 8) &&
        response.stop == (if reason == "max_tokens" then .maxTokens else .contextOverflow)
      let initial := init "stream-limit" {
        model := "fixture", workspace := "/tmp/fixture"
        maxResponseRepairs := 2, compactionEnabled := false} "task"
      let reserved ← match step initial with
        | ⟨.control, next⟩ => pure (next {})
        | _ => throw (IO.userError "expected control before model admission")
      let rejected ← match step reserved with
        | ⟨.model _, next⟩ => pure (next (.success response))
        | _ => throw (IO.userError "expected reserved model attempt")
      check "earlier complete mutation gains no authority" <|
        rejected.modelAttempts == 1 && rejected.toolDispatches == 0 &&
        rejected.seenCallIds.isEmpty && rejected.grant.isNone && rejected.unknownUsage == 0 &&
        rejected.knownInputTokens == 12 && rejected.knownOutputTokens == 8
      if reason == "max_tokens" then
        check "truncation repairs only prior valid history" <|
          rejected.responseRepairs == 1 &&
          toJson rejected.history == toJson (initial.history ++ [responseRepairMessage .truncated])
        let cancelled ← match step rejected with
          | ⟨.control, next⟩ => pure (next {cancelled := true})
          | _ => throw (IO.userError "repair bypassed cancellation control")
        check "cancel before repaired attempt emits no work" <|
          cancelled.modelAttempts == 1 && cancelled.toolDispatches == 0 &&
          (match (step cancelled).1 with | .finish .cancelled => true | _ => false)
      else
        check "context overflow remains a terminal limit" <|
          rejected.responseRepairs == 0 && toJson rejected.history == toJson initial.history &&
          (match (step rejected).1 with | .finish (.limit _) => true | _ => false)
  for reason in ["end_turn", "tool_use"] do
    check "successful stop cannot authorize an open batch" (fails (incompleteBatch ++ terminal reason))
  check "limit requires final message stop" (fails (incompleteBatch ++ terminalDelta "max_tokens"))
  check "limit requires validated terminal delta" (fails (incompleteBatch ++ event "message_stop"))
  for late in [delta 1 "input_json_delta" "partial_json" "null}", stopBlock 1] do
    check "content cannot change after terminal limit" <|
      fails (incompleteBatch ++ terminalDelta "max_tokens" ++ late ++ event "message_stop")
  check "open limit cannot conceal resource refusal" <| fails (start ++ toolStart ++
    delta 0 "input_json_delta" "partial_json" "{\"n\":1e50000," ++ terminal "max_tokens")
  let emptyTerminalUsage := event "message_delta" [
    ("delta", Json.mkObj [("stop_reason", toJson "end_turn")]), ("usage", Json.mkObj [])] ++ event "message_stop"
  check "initial output zero cannot replace missing final usage" (fails (start ++ emptyTerminalUsage))
  let invalidTerminalUsage := event "message_delta" [
    ("delta", Json.mkObj [("stop_reason", toJson "end_turn")]),
    ("usage", Json.mkObj [("output_tokens", toJson (1 : Nat)),
      ("cache_creation_input_tokens", toJson (-1 : Int))])] ++ event "message_stop"
  check "new negative usage counter rejected" (fails (start ++ invalidTerminalUsage))
  let wrongTypeUsage := event "message_delta" [
    ("delta", Json.mkObj [("stop_reason", toJson "end_turn")]),
    ("usage", Json.mkObj [("output_tokens", toJson "8")])] ++ event "message_stop"
  check "wrong-type terminal output usage rejected" (fails (start ++ wrongTypeUsage))
  let thinking := start ++ block 0 (Json.mkObj [("type", toJson "thinking"), ("thinking", toJson ""),
    ("signature", toJson ""), ("opaque", toJson "preserve")]) ++
    delta 0 "thinking_delta" "thinking" "secret reasoning" ++ delta 0 "signature_delta" "signature" "sig-" ++
    delta 0 "signature_delta" "signature" "λ" ++ stopBlock 0 ++
    block 1 (Json.mkObj [("type", toJson "redacted_thinking"), ("data", toJson "opaque-base64")]) ++ stopBlock 1 ++ terminal
  let (thoughts, progress) ← IO.ofExcept (decode #[thinking.toUTF8])
  check "thinking not exposed as progress" progress.isEmpty
  check "malformed present signature is not silently rewritten" <| fails (start ++
    block 0 (Json.mkObj [("type", toJson "thinking"), ("thinking", toJson ""),
      ("signature", toJson (42 : Nat))]) ++ stopBlock 0 ++ terminal)
  let contents ← IO.ofExcept (thoughts.getObjValAs? (Array Json) "content")
  check "signature assembled and opaque fields preserved" <|
    (contents[0]!.getObjValAs? String "signature").toOption == some "sig-λ" &&
    (contents[0]!.getObjValAs? String "opaque").toOption == some "preserve" &&
    (contents[1]!.getObjValAs? String "data").toOption == some "opaque-base64"
  check "missing final terminal" (fails (start ++ toolStart ++ stopBlock 0))
  check "open block at terminal" (fails (start ++ toolStart ++ terminal))
  check "duplicate start" (fails (start ++ start ++ terminal))
  check "out of order block" (fails (start ++ stopBlock 0 ++ terminal))
  check "wrong block index" (fails (start ++ toolStart ++ stopBlock 1 ++ terminal))
  check "event after terminal" (fails (textStream ++ toolStart))
  check "unterminated trailing data" (fails (textStream ++ "data: {}"))
  check "unknown semantics fail closed" (fails (textStream ++ event "future_event"))
  check "event type mismatch" (fails (textStream.replace "event: message_stop" "event: message_delta"))
  check "invalid UTF8" ((decode #[bytes ++ ByteArray.mk #[255, 10]]).toOption.isNone)
  let (state, _) ← IO.ofExcept <| Harness.SSE.feed {} (start ++ event "error" [
    ("error", Json.mkObj [("type", toJson "overloaded_error")])]).toUTF8
  check "stream overload classified without successful response" (state.serverError == some .transport && (Harness.SSE.finish state).toOption.isNone)
  IO.println "SSE contracts passed (all byte splits, opaque blocks, bounds, malformed lifecycles)."

end Tests.SSE
