import Harness.Core.Protocol

/-!
The normalized assistant-content contract is enforced in the core as well as used
by provider normalization. Blocks are inspected without rebuilding them, so opaque
reasoning/signature content remains available for the next provider request.
-/
namespace Harness
open Lean

private def contentString (json : Json) (key : String) : Except String String := do
  (← json.getObjVal? key).getStr?

/-- Decode the supported complete assistant blocks in their original order.
This function never authorizes a tool; argument and batch validation remain in Policy. -/
def parseModelContent (blocks : Array Json) : Except String (List RawCall × String) := do
  let mut calls := []
  let mut text := ""
  for block in blocks do
    let kind ← contentString block "type"
    match kind with
    | "text" => text := text ++ (← contentString block "text")
    | "thinking" =>
      let _ ← contentString block "thinking"
      let _ ← contentString block "signature"
    | "redacted_thinking" =>
      let _ ← contentString block "data"
    | "tool_use" =>
      let id ← contentString block "id"
      let name ← contentString block "name"
      let input ← block.getObjVal? "input"
      match input with
      | .obj _ => pure ()
      | _ => throw "tool_use input must be an object"
      calls := calls ++ [{ id := id, name := name, input := input }]
    | _ => throw s!"unsupported content block: {kind}"
  return (calls, text)

/-- Call identity includes the complete encoded arguments, not only the tool name.
JSON objects are emitted in key order by Lean's serializer. Equality is deliberately
wire-level equality; this does not assume a theorem about Lean's opaque Json BEq. -/
def RawCall.descriptor (call : RawCall) : String × String × String :=
  (call.id, call.name, call.input.compress)

/-- The retained content and normalized fields describe the same ordered calls/text.
This is the local accepted-response contract, not a whole-history pairing invariant. -/
def ModelResponseConsistent (response : ModelResponse) : Prop :=
  ∃ decoded : List RawCall × String,
    parseModelContent response.content = .ok decoded ∧
    decoded.1.map RawCall.descriptor = response.calls.map RawCall.descriptor ∧
    decoded.2 = response.text

/-- Check even already-typed observations: adapters and journal records can supply
inconsistent redundant fields. A mismatch must not enter authoritative history. -/
def validateModelResponse (response : ModelResponse) : Except String Unit :=
  match parseModelContent response.content with
  | .error message => .error message
  | .ok (calls, text) =>
    if calls.map RawCall.descriptor ≠ response.calls.map RawCall.descriptor then
      .error "content tool calls disagree with normalized calls"
    else if text ≠ response.text then
      .error "content text disagrees with normalized text"
    else .ok ()

end Harness
