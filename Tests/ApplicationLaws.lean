import Harness.Proofs.ApplicationCoding
import Harness.Proofs.ApplicationInventory
import Harness.Proofs.ApplicationRendering

namespace Tests.ApplicationLaws
open Lean Harness

example (op : ToolOp) : (fromJson? (toJson op) : Except String ToolOp) = .ok op :=
  Coding.operation_roundtrip op

example (op : Inventory.Operation) (result : Inventory.Result op)
    (valid : Inventory.validResult op result = true) :
    Inventory.decodeResult op (Inventory.encodeResult op result) = .ok result :=
  Inventory.result_roundtrip op result valid

example (app : Application) (laws : ApplicationLaws app) (call : Call app)
    (validOp : laws.ValidOperation call.operation) (response : ToolObservation (app.Result call.operation))
    (valid : laws.ValidObservation call.operation response) :
    replyFromJson (.tool call) (replyToJson (.tool call) response) = .ok response :=
  application_tool_reply_roundtrip laws call validOp response valid

private def check (message : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError message)

private def item : Inventory.Item :=
  {sku := "A", name := "Widget", warehouse := "N", onHand := 2, reorderPoint := 5}

private def config : Config := {model := "scripted", maxToolCalls := 10, executionProfile := .bubblewrap}
private def call : ToolCall := ⟨"actual", .runProcess {argv := #["true"]}⟩
private def skipped : ToolCall := ⟨"skipped", .createFile {path := "next", content := "x"}⟩
private def state : State := {init "test" config "task" with phase := .tool call [skipped], toolDispatches := 1}

def run : IO Unit := do
  let badLookup := Inventory.encodeResult (.lookup "B") (some item)
  check "unrestricted lookup roundtrip must reject a mismatched SKU"
    (Inventory.decodeResult (.lookup "B") badLookup).toOption.isNone
  let page : Inventory.StockPage := {
    rows := #[{item, units := 3}], matched := 2, offset := 0, nextOffset := some 0, truncated := true}
  check "page continuation must progress"
    (Inventory.decodeResult (.lowStock "N" 0 1) (Inventory.encodeResult (.lowStock "N" 0 1) page)).toOption.isNone
  let badReceipt : Inventory.Reservation := {
    sessionId := "session", operationId := 1, sku := "A", units := 3, before := 7, remaining := 7}
  check "typed receipt cannot establish impossible stock arithmetic"
    (Inventory.decodeResult (.reserve "A" 3) (Inventory.encodeResult (.reserve "A" 3) badReceipt)).toOption.isNone
  check "typed coding operation still needs independent validity"
    (Coding.decodeOperation {id := "x", name := "read", input := Json.mkObj [("path", toJson "../escape")]}).toOption.isNone
  let largeTotals := Json.mkObj [("kind", toJson "warehouse_totals"),
    ("warehouses", .arr (Array.replicate 65 .null))]
  check "totals size rejection precedes nested parsing" <|
    match Inventory.decodeResult .warehouseTotals largeTotals with
    | .error message => message == "too many warehouse summaries"
    | .ok _ => false
  let largePage := Json.mkObj [("kind", toJson "low_stock"), ("page", Json.mkObj [
    ("rows", .arr (Array.replicate 101 .null)), ("matched", toJson (101 : Nat)),
    ("offset", toJson (0 : Nat)), ("nextOffset", toJson (some (50 : Nat))), ("truncated", toJson true)])]
  check "page size rejection precedes nested parsing" <|
    match Inventory.decodeResult (.lowStock "N" 0 50) largePage with
    | .error message => message == "too many low-stock rows"
    | .ok _ => false
  let raw : ToolResult := {text := "partial", exitCode := some 23, sha256 := some "not-established"}
  let timed := consumeTool state call [skipped] (.timedOut (some raw))
  let visible := visibleToolResults timed.history
  check "timeout closes actual and skipped calls in order"
    (visible.map (·.id) == ["actual", "skipped"] && visible.all (·.isError))
  check "skipped call does not consume dispatch budget" (timed.toolDispatches == 1)
  check "timeout clears exit and file-hash assertions"
    ((timeoutResultAndArtifacts state (some raw)).1.exitCode.isNone &&
      (timeoutResultAndArtifacts state (some raw)).1.sha256.isNone)
  let uncertain := consumeTool state call [skipped] (.uncertain "lost" (some raw))
  check "uncertainty cannot fabricate a completed model-visible result"
    (visibleToolResults uncertain.history).isEmpty
  let cancelled := cancelCalls state [call, skipped]
  check "cancellation records exact undispatched errors"
    ((visibleToolResults cancelled.history).map (·.content) == [cancelledCallText, cancelledCallText])
  let malformed : ToolResult := {text := "original", artifacts := #[{
    id := "bad", sha256 := "bad", label := "stdout", storedBytes := 9, totalBytes := 1, truncated := false}]}
  let rejected := consumeTool state call [] (.success malformed)
  check "artifact rejection is model-visible error"
    ((visibleToolResults rejected.history).map (·.isError) == [true] && rejected.artifacts.isEmpty)
  IO.println "Application law boundary checks passed (12)."

end Tests.ApplicationLaws
