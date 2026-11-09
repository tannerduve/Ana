import Harness.Adapter.Provider

/-!
Bounded, pure decoding of Anthropic's documented SSE message protocol. Byte chunks
may end anywhere, including inside UTF-8 or CRLF. Only text deltas are provisional;
`finish` requires the whole message lifecycle before returning complete JSON for
the existing provider/core validators. Unknown semantic events fail closed.
-/
namespace Harness.SSE
open Lean

private structure Block where
  raw : Json
  kind : String
  text : Array String := #[]
  signature : Array String := #[]
  input : Array String := #[]
  deriving Repr

structure State where
  maximumBytes : Nat := 2000000
  received : Nat := 0
  /-- Shared by outer event JSON and the final tool-argument reparses. -/
  numericWork : Nat := 0
  line : ByteArray := ByteArray.empty
  afterCR : Bool := false
  firstLine : Bool := true
  event : Option String := none
  dataLines : Array String := #[]
  message : Option Json := none
  blocks : Array Block := #[]
  active : Option Block := none
  deltaSeen : Bool := false
  stopped : Bool := false
  serverError : Option FailureClass := none

private def field (j : Json) (name : String) : Except String String :=
  (j.getObjVal? name).bind Json.getStr?

private def object (j : Json) : Except String Unit :=
  match j with
  | .obj _ => .ok ()
  | _ => .error "expected JSON object"

private def validateUsage (usage : Json) : Except String Unit := do
  object usage
  for key in ["input_tokens", "output_tokens", "cache_creation_input_tokens", "cache_read_input_tokens"] do
    if let some value := (usage.getObjVal? key).toOption then
      let _ ← value.getNat?
      pure ()

private def limitStop (stop : Json) : Bool :=
  stop == toJson "max_tokens" || stop == toJson "model_context_window_exceeded"

private def join (parts : Array String) : String := String.join parts.toList

private def blockStart (j : Json) : Except String Block := do
  let kind ← field j "type"
  match kind with
  | "text" => return { raw := j, kind, text := #[← field j "text"] }
  | "thinking" =>
    let signature ← match (j.getObjVal? "signature").toOption with
      | none => pure ""
      | some value => value.getStr?
    return { raw := j, kind, text := #[← field j "thinking"], signature := #[signature] }
  | "redacted_thinking" =>
    let _ ← field j "data"
    return { raw := j, kind }
  | "tool_use" =>
    let _ ← field j "id"
    let _ ← field j "name"
    object (← j.getObjVal? "input")
    return { raw := j, kind }
  | _ => throw "unsupported streamed content block"

private def blockDelta (block : Block) (delta : Json) : Except String (Block × Array String) := do
  let kind ← field delta "type"
  match block.kind, kind with
  | "text", "text_delta" =>
    let text ← field delta "text"
    return ({block with text := block.text.push text}, #[text])
  | "thinking", "thinking_delta" =>
    return ({block with text := block.text.push (← field delta "thinking")}, #[])
  | "thinking", "signature_delta" =>
    return ({block with signature := block.signature.push (← field delta "signature")}, #[])
  | "tool_use", "input_json_delta" =>
    unless (← block.raw.getObjVal? "input") == Json.mkObj [] do
      throw "streamed input cannot replace nonempty initial tool arguments"
    return ({block with input := block.input.push (← field delta "partial_json")}, #[])
  | _, _ => throw "unsupported or mismatched content delta"

private def finishBlock (block : Block) (truncated : Bool) (spent : Nat) :
    Except String (Json × Nat) := do
  match block.kind with
  | "text" => return (block.raw.mergeObj (Json.mkObj [("text", toJson (join block.text))]), spent)
  | "thinking" => return (block.raw.mergeObj (Json.mkObj [
      ("thinking", toJson (join block.text)), ("signature", toJson (join block.signature))]), spent)
  | "tool_use" =>
    if block.input.isEmpty then return (block.raw, spent)
    let text := join block.input
    -- Resource refusal remains an error even for truncated responses. Only an
    -- admitted but grammatically incomplete argument retains the old stop class.
    let work ← JsonBounds.checkWork text spent
    let input ← match Json.parse text with
      | .ok value => pure value
      | .error _ =>
        if truncated then pure (toJson text)
        else throw "incomplete streamed tool JSON"
    unless truncated do object input
    return (block.raw.mergeObj (Json.mkObj [("input", input)]), work)
  | _ => return (block.raw, spent)

private def applyEvent (state : State) (name : String) (j : Json) :
    Except String (State × Array String) := do
  unless (← field j "type") == name do throw "SSE event name/type mismatch"
  if name == "ping" then return (state, #[])
  if state.stopped || state.serverError.isSome then throw "semantic event after stream termination"
  if name == "error" then
    let kind ← field (← j.getObjVal? "error") "type"
    let failure := match kind with
      | "rate_limit_error" => FailureClass.rateLimit
      | "overloaded_error" | "api_error" => FailureClass.transport
      | "authentication_error" | "permission_error" => FailureClass.authentication
      | "invalid_request_error" => FailureClass.invalidRequest
      | _ => FailureClass.other
    return ({state with serverError := some failure}, #[])
  if name == "message_start" then
    if state.message.isSome then throw "duplicate message_start"
    let message ← j.getObjVal? "message"
    unless (← field message "type") == "message" && (← field message "role") == "assistant" do
      throw "invalid streaming message header"
    unless (← (← message.getObjVal? "content").getArr?).isEmpty do
      throw "message_start content must be empty"
    unless (← message.getObjVal? "stop_reason") == .null do
      throw "message_start already contains stop reason"
    if let some usage := (message.getObjVal? "usage").toOption then validateUsage usage
    return ({state with message := some message}, #[])
  let some message := state.message | throw "stream event before message_start"
  if name == "content_block_start" then
    if state.active.isSome || state.deltaSeen then throw "content block outside content phase"
    unless (← j.getObjValAs? Nat "index") == state.blocks.size do throw "nonsequential content index"
    let block ← blockStart (← j.getObjVal? "content_block")
    let provisional := if block.kind == "text" then block.text else #[]
    return ({state with active := some block}, provisional)
  if name == "content_block_delta" || name == "content_block_stop" then
    if state.deltaSeen then throw "content event after terminal delta"
    let some block := state.active | throw "content event without an active block"
    unless (← j.getObjValAs? Nat "index") == state.blocks.size do throw "content index mismatch"
    if name == "content_block_stop" then
      return ({state with active := none, blocks := state.blocks.push block}, #[])
    let (updated, text) ← blockDelta block (← j.getObjVal? "delta")
    return ({state with active := some updated}, text)
  if name == "message_delta" then
    let delta ← j.getObjVal? "delta"
    object delta
    -- Preserve additive terminal metadata, but never replace identity or content.
    for key in ["type", "role", "id", "model", "content", "usage"] do
      if (delta.getObjVal? key).toOption.isSome then throw "terminal delta replaces protected message field"
    let oldStop ← message.getObjVal? "stop_reason"
    let stop := (delta.getObjVal? "stop_reason").toOption.getD oldStop
    if stop != .null then
      let _ ← stop.getStr?
      pure ()
    if oldStop != .null && stop != oldStop then throw "terminal stop reason changed"
    let stopSequence := (delta.getObjVal? "stop_sequence").toOption.getD .null
    let usage ← j.getObjVal? "usage"
    validateUsage usage
    -- Anthropic's message_delta contract requires cumulative output_tokens. The
    -- initial zero is only provisional and cannot stand in for missing final usage.
    let _ ← usage.getObjValAs? Nat "output_tokens"
    let oldUsage := (message.getObjVal? "usage").toOption.getD (Json.mkObj [])
    validateUsage oldUsage
    for key in ["input_tokens", "output_tokens", "cache_creation_input_tokens", "cache_read_input_tokens"] do
      if let some previous := (oldUsage.getObjValAs? Nat key).toOption then
        if let some next := (usage.getObjVal? key).toOption then
          let next ← next.getNat?
          if next < previous then throw "cumulative streamed usage decreased"
    -- A provider may hit its output limit before closing the final block. This
    -- remains non-executable truncation, with terminal metadata validated here
    -- and final message_stop/HTTP completion still required by the caller.
    if state.active.isSome then
      unless limitStop stop do throw "message delta before content block stop"
      let _ ← (oldUsage.mergeObj usage).getObjValAs? Nat "input_tokens"
      pure ()
    let updated := (message.mergeObj delta).mergeObj (Json.mkObj [("stop_reason", stop),
      ("stop_sequence", stopSequence), ("usage", oldUsage.mergeObj usage)])
    return ({state with message := some updated, deltaSeen := true}, #[])
  if name == "message_stop" then
    if !state.deltaSeen || (state.active.isSome && !limitStop (← message.getObjVal? "stop_reason")) then
      throw "message_stop before complete terminal delta"
    return ({state with stopped := true}, #[])
  throw "unsupported SSE event"

private def dispatch (state : State) : Except String (State × Array String) := do
  if state.dataLines.isEmpty then
    if state.event.isSome then throw "SSE event has no data"
    return (state, #[])
  let some name := state.event | throw "SSE data has no event name"
  let data := String.intercalate "\n" state.dataLines.toList
  let (json, work) ← JsonBounds.parseWithWork data state.numericWork
  applyEvent {state with event := none, dataLines := #[], numericWork := work} name json

private def acceptLine (state : State) (bytes : ByteArray) : Except String (State × Array String) := do
  let bytes := if bytes.size > 0 && bytes[bytes.size - 1]! == 13 then bytes.extract 0 (bytes.size - 1) else bytes
  let some line := String.fromUTF8? bytes | throw "invalid UTF-8 in SSE stream"
  let line := if state.firstLine && line.startsWith (String.singleton (Char.ofNat 0xFEFF)) then (line.drop 1).toString else line
  let state := {state with firstLine := false}
  if line.isEmpty then return ← dispatch state
  if line.startsWith ":" then return (state, #[])
  let parts := line.splitOn ":"
  let name := parts.head!
  let value := String.intercalate ":" parts.tail
  let value := if value.startsWith " " then (value.drop 1).toString else value
  if name == "event" then
    if state.event.isSome then throw "duplicate SSE event field"
    return ({state with event := some value}, #[])
  if name == "data" then return ({state with dataLines := state.dataLines.push value}, #[])
  -- Standard transport-only metadata does not change model semantics.
  if name == "id" || name == "retry" then return (state, #[])
  throw "unsupported SSE field"

/-- Consume bounded bytes. No incomplete content can be returned as an accepted
response; the returned strings are explicitly provisional display text only. -/
def feed (state : State) (chunk : ByteArray) : Except String (State × Array String) := do
  if state.received + chunk.size > state.maximumBytes then throw "SSE response byte limit exceeded"
  let mut current := {state with received := state.received + chunk.size}
  let mut provisional := #[]
  for byte in chunk do
    if byte == 10 && current.afterCR then
      current := {current with afterCR := false}
    else if byte == 10 || byte == 13 then
      let (next, text) ← acceptLine {current with line := ByteArray.empty, afterCR := byte == 13} current.line
      current := next
      provisional := provisional ++ text
    else
      current := {current with line := current.line.push byte, afterCR := false}
  return (current, provisional)

/-- Called only after HTTP transport completes. A terminal limit may leave the
last block open; in that case all content is discarded after resource checks.
No incomplete frame, successful open block, or partial tool batch is admitted. -/
def finish (state : State) : Except String Json := do
  unless state.serverError.isNone && state.stopped && state.line.isEmpty &&
      state.event.isNone && state.dataLines.isEmpty do throw "incomplete SSE message"
  let some message := state.message | throw "missing streamed message"
  let stop ← field message "stop_reason"
  let truncated := limitStop (toJson stop)
  if state.active.isSome && !truncated then throw "incomplete SSE message"
  let mut blocks := #[]
  let mut work := state.numericWork
  for block in state.blocks do
    let (value, nextWork) ← finishBlock block truncated work
    blocks := blocks.push value
    work := nextWork
  if let some active := state.active then
    -- Earlier complete calls and the final partial call are one discarded batch.
    -- Preserve numeric-work refusal even though none of these arguments execute.
    let _ ← finishBlock active true work
    return message.mergeObj (Json.mkObj [("content", toJson (#[] : Array Json))])
  return message.mergeObj (Json.mkObj [("content", toJson blocks)])

end Harness.SSE
