import Plausible.Testable
import Harness.Adapter.Provider
import Harness.Core.Transition

/-!
Runtime property tests, not theorem declarations. Fixed seeds make failures
reproducible; Plausible generates and shrinks values, and an inconclusive suite
fails the executable. Expected values come from source fixtures, not the decoder.
-/
namespace Tests.Properties
open Lean Harness Plausible

private def initial : State :=
  admitModel (init "generated-provider-contract" { model := "generated", workspace := "/tmp/generated" }
    "inspect the repository")

private def difficultText (text : String) : String :=
  "quote=\" slash=\\ newline=\n unicode=λ🙂 " ++ text

private def rawResponse (content : Array Json) (stop : String) : Json :=
  Json.mkObj [("type", toJson "message"), ("role", toJson "assistant"),
    ("content", toJson content), ("stop_reason", toJson stop)]

private def normalize (content : Array Json) (stop : String) : ModelObservation :=
  Provider.normalizeHttp 200 (rawResponse content stop).compress

private def textContract (sample : String × List String) : Bool :=
  let signature := difficultText sample.1
  let pieces := (sample.2.take 8).map difficultText
  let blocks := #[Json.mkObj [("type", toJson "thinking"), ("thinking", toJson sample.1),
      ("signature", toJson signature)],
    Json.mkObj [("type", toJson "redacted_thinking"), ("data", toJson signature)]] ++
    (pieces.map Harness.textBlock).toArray
  let expected := String.intercalate "" pieces
  let received := consumeModel initial (normalize blocks "end_turn")
  let history := initial.history ++ [{ role := "assistant", content := blocks }]
  let wire := Provider.encodeRequest { model := "generated", system := signature, messages := history, maxTokens := 100 }
  (match received.phase with | .stopped (.final actual) => actual == expected | _ => false) &&
    toJson received.history == toJson history &&
    (wire.getObjVal? "messages").toOption == some (toJson history) &&
    (wire.getObjValAs? String "system").toOption == some signature

private def createBlock (index : Nat) (content : String) : Json :=
  Json.mkObj [("type", toJson "tool_use"), ("id", toJson s!"create-{index}"),
    ("name", toJson "create"), ("input", Json.mkObj [("path", toJson s!"file-{index}.txt"),
      ("content", toJson content)])]

private def contents (sample : String × List String) : List String :=
  (sample.1 :: sample.2.take 7).map difficultText

private def batch (sample : String × List String) : Array Json :=
  ((contents sample).zipIdx.map fun (content, index) => createBlock index content).toArray

private def batchContract (sample : String × List String) : Bool :=
  let blocks := batch sample
  let expected : List ToolCall := (contents sample).zipIdx.map fun (content, index) =>
    { id := s!"create-{index}", operation := .createFile { path := s!"file-{index}.txt", content } }
  let received := consumeModel initial (normalize blocks "tool_use")
  (match received.phase with
    | .controlTools calls => toJson calls == toJson expected
    | _ => false) &&
    received.seenCallIds == expected.map (·.id) && received.toolDispatches == 0 &&
    toJson received.history == toJson (initial.history ++ [{ role := "assistant", content := blocks }])

private def rejectedBatchContract (sample : (String × List String) × Nat) : Bool :=
  let blocks := batch sample.1
  let invalid := match sample.2 % 4 with
    | 0 => createBlock 0 "same identity with different content"
    | 1 => Json.mkObj [("type", toJson "tool_use"), ("id", toJson "bad"),
        ("name", toJson "create"), ("input", Json.mkObj [("path", toJson "missing-content.txt")])]
    | 2 => Json.mkObj [("type", toJson "tool_use"), ("id", toJson "bad"),
        ("name", toJson "unregistered-tool"), ("input", Json.mkObj [])]
    | _ => Json.mkObj [("type", toJson "tool_use"), ("input", toJson "truncated")]
  let reason := if sample.2 % 4 == 3 then "max_tokens" else "tool_use"
  let received := consumeModel initial (normalize (blocks.push invalid) reason)
  (match received.phase with | .stopped (.failure _) => true | _ => false) &&
    received.toolDispatches == 0 && received.seenCallIds.isEmpty &&
    toJson received.history == toJson initial.history

private def checkProperty (label : String) (property : Prop) [Testable property]
    (seed : Nat) : IO Unit := do
  let result ← Testable.checkIO property {
    numInst := 300, maxSize := 32, randomSeed := some seed }
  match result with
  | .success _ => pure ()
  | .gaveUp count => throw <| IO.userError s!"property {label} seed={seed} gave up after {count} discarded samples"
  | .failure _ examples shrinks =>
    throw <| IO.userError s!"property {label} seed={seed} failed after {shrinks} shrinks: {examples}"

def run : IO Unit := do
  checkProperty "text and opaque block roundtrip"
    (NamedBinder "sample" (∀ sample : String × List String, textContract sample = true)) 41001
  checkProperty "ordered create arguments and admission"
    (NamedBinder "sample" (∀ sample : String × List String, batchContract sample = true)) 41002
  checkProperty "all-or-none malformed batch rejection"
    (NamedBinder "sample" (∀ sample : (String × List String) × Nat, rejectedBatchContract sample = true)) 41003
  IO.println "properties: 900 Plausible-generated provider/core cases passed (seeds 41001–41003)"

end Tests.Properties
