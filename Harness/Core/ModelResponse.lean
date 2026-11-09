import Harness.Core.Protocol

/-!
Decodes supported assistant content blocks (text, thinking, redacted thinking, tool use) in order,
leaving opaque blocks unchanged. `validateModelResponse` rejects responses whose normalized calls or
text disagree with the retained content, compared at the wire level. Tool authorization is left to
`Policy`.
-/

namespace Harness
open Lean

def contentString (json : Json) (key : String) : Except String String := do
  (← json.getObjVal? key).getStr?

/-- One complete supported block. Opaque fields remain in the original JSON;
this fold accumulates only normalized calls and text. -/
def parseContentBlock (acc : List RawCall × String) (block : Json) :
    Except String (List RawCall × String) := do
  let kind ← contentString block "type"
  match kind with
  | "text" => return (acc.1, acc.2 ++ (← contentString block "text"))
  | "thinking" =>
    let _ ← contentString block "thinking"
    let _ ← contentString block "signature"
    return acc
  | "redacted_thinking" =>
    let _ ← contentString block "data"
    return acc
  | "tool_use" =>
    let id ← contentString block "id"
    let name ← contentString block "name"
    let input ← block.getObjVal? "input"
    match input with
    | .obj _ => pure ()
    | _ => throw "tool_use input must be an object"
    return (acc.1 ++ [{ id := id, name := name, input := input }], acc.2)
  | _ => throw s!"unsupported content block: {kind}"

/-- Decode the supported complete assistant blocks in their original order.
This function never authorizes a tool; argument and batch validation remain in Policy. -/
def parseModelContent (blocks : Array Json) : Except String (List RawCall × String) :=
  blocks.toList.foldlM parseContentBlock ([], "")

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
