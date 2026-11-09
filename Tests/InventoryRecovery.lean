import Harness.Runner
import Harness.Applications.InventoryIO
import Harness.Applications.InventoryStoreIO

/-!
Real IO and process-boundary tests for inventory reservations. Child processes run the actual
shared Runner with scripted model responses. A test-only runtime wrapper exits after the real
store commit but before the Runner can append completion; production has no fault-injection flag.
The tests assert receipt reconciliation, not exactly-once execution of arbitrary side effects.
-/
namespace Tests.InventoryRecovery
open Lean Harness

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError s!"inventory recovery contract: {label}"

private def seed : Inventory.Dataset := {version := 1, items := #[
  {sku := "SKU-A", name := "Item A", warehouse := "north", onHand := 10, reorderPoint := 12},
  {sku := "SKU-B", name := "Item B", warehouse := "north", onHand := 9, reorderPoint := 4}]}

private def config (mode : String) : Config := {
  model := "scripted-inventory-recovery"
  instructions := Inventory.application.defaultInstructions
  applicationData := toJson seed
  toolPolicy := if mode == "deny" then .deny else .allow
  maxModelAttempts := 4
  maxToolCalls := 4
  maxContextBytes := 1000000
  maxToolOutputBytes := if mode == "output-bound" then 32 else 65536
  maxElapsedMs := 30000
  operationTimeoutMs := 5000
  maxRetries := 0
  maxResponseRepairs := 0
  compactionEnabled := false}

private def call (id name : String) (fields : List (String × Json)) : Json :=
  Json.mkObj [("type", toJson "tool_use"), ("id", toJson id), ("name", toJson name),
    ("input", Json.mkObj fields)]

private def response (blocks : Array Json) (stop : String) : Json := Json.mkObj [
  ("type", toJson "message"), ("role", toJson "assistant"), ("content", toJson blocks),
  ("stop_reason", toJson stop),
  ("usage", Json.mkObj [("input_tokens", toJson (1 : Nat)), ("output_tokens", toJson (1 : Nat))])]

private def script (mode : String) : Array Json := #[
  response #[call "reserve-1" "reserve" [("sku", toJson "SKU-A"),
    ("units", toJson (if mode == "insufficient" then 11 else 3 : Nat))]] "tool_use",
  response #[call "lookup-1" "lookup" [("sku", toJson "SKU-A")],
    call "stock-1" "low_stock" [("warehouse", toJson "north"), ("offset", toJson (0 : Nat)),
      ("limit", toJson (10 : Nat))]] "tool_use",
  response #[textBlock "Inventory reservation and follow-up queries inspected."] "end_turn"]

/-- Exit bypasses the Runner's completion append and all Lean finally blocks.
This models a stopped process at a durable cutpoint, not a power-loss experiment. -/
private def childRuntime (mode : String) : ApplicationIO.Runtime Inventory.application :=
  {InventoryIO.runtime with execute := fun cfg context operation => do
    match operation.operation with
    | .reserve _ _ =>
      if mode == "before" then IO.Process.exit 92
      let observed ← InventoryIO.runtime.execute cfg context operation
      match observed with
      | .success result =>
        if mode == "after" then IO.Process.exit 91
        if mode == "uncertain" then
          return .uncertain "test lost acknowledgement after durable reservation" (some result)
        return observed
      | _ => return observed
    | _ => InventoryIO.runtime.execute cfg context operation}

private def child (arguments : List String) : IO UInt32 := do
  let output ← EventIO.create
  try
    let code ← match arguments with
      | ["start", mode, session] =>
        Runner.start (childRuntime mode) {session, output, script := some (script mode)}
          (config mode) "Reserve three units of SKU-A, then query its remaining stock and replenishment need."
      | ["resume", session] => Runner.resume InventoryIO.runtime {session, output}
      | _ => throw <| IO.userError "invalid inventory-recovery child arguments"
    let delivered ← EventIO.finish output
    return if code == 0 && !delivered then 74 else code
  finally EventIO.close output

private def invoke (executable : String) (arguments : Array String) (expected : UInt32) : IO Unit := do
  let observation ← ProcessIO.capture {
    cmd := executable, args := #["--child"] ++ arguments
    timeoutMs := 30000, cancelPath := "", stdoutBytes := 1048576, stderrBytes := 65536
    includeHome := false}
  check s!"child {arguments.toList}: expected {expected}; got {observation.exitCode}; {String.fromUTF8! observation.stderr}"
    (observation.status == .completed && observation.exitCode == some expected)
  check "child output was truncated" (observation.stdoutTotal == observation.stdout.size)

private def journal (session : System.FilePath) : IO (Array Json) :=
  return (← JournalIO.read (session / "journal.jsonl").toString).records

private def store (session : System.FilePath) : IO (Array Json) := do
  if !(← (session / "inventory.jsonl").pathExists) then return #[]
  let result ← JournalIO.read (session / "inventory.jsonl").toString
  check "inventory receipt log has an interrupted tail" (!result.interrupted)
  return result.records

private def load (output : EventIO.Output) (session : System.FilePath) :
    IO (Runner.Loaded Inventory.application) :=
  Runner.load Inventory.application {session := session.toString, output} true

private def results (state : State Inventory.application) (id : String) : Array Json :=
  state.history.toArray.foldl (fun acc message =>
    acc ++ message.content.filter (fun block =>
      (block.getObjValAs? String "tool_use_id").toOption == some id)) #[]

private def resultValue (state : State Inventory.application) (id : String) : IO Json := do
  let values := results state id
  check s!"expected exactly one authoritative result for {id}" (values.size == 1)
  let outer ← IO.ofExcept <| JsonBounds.parse (← IO.ofExcept <| values[0]!.getObjValAs? String "content")
  IO.ofExcept <| JsonBounds.parse (← IO.ofExcept <| outer.getObjValAs? String "text")

private def isFinal (state : State Inventory.application) : Bool :=
  match state.phase with | .stopped (.final _) => true | _ => false

private def checkpoint (output : EventIO.Output) (session : System.FilePath) :
    IO (State Inventory.application) := do
  let loaded ← load output session
  let some prior := Recovery.target loaded.cursor
    | throw <| IO.userError "crash fixture has no unresolved operation"
  check "crash did not retain its exact budget reservation"
    (prior.modelAttempts == 1 && prior.toolDispatches == 1)
  match (step prior).1 with
  | .tool operation =>
    check "wrong interrupted operation"
      (operation.id == "reserve-1" && operation.operation == .reserve "SKU-A" 3)
  | _ => throw <| IO.userError "crash fixture is not awaiting a tool result"
  return prior

private def verifyFinished (output : EventIO.Output) (session : System.FilePath) : IO Unit := do
  let loaded ← load output session
  let state := loaded.cursor.state
  check "reservation recovery did not finish" (loaded.cursor.terminal && isFinal state)
  check "recovery refunded or repeated a reserved dispatch"
    (state.modelAttempts == 3 && state.toolDispatches == 3 && state.unknownUsage == 0)
  let receipt ← IO.ofExcept <| (← resultValue state "reserve-1").getObjValAs? Inventory.Reservation "reservation"
  check "wrong authoritative receipt" (receipt.sku == "SKU-A" && receipt.units == 3 &&
    receipt.before == 10 && receipt.remaining == 7 && receipt.sessionId == session.toString)
  let found ← IO.ofExcept <| (← resultValue state "lookup-1").getObjValAs? Inventory.Item "item"
  check "query did not observe committed debit, or debit repeated" (found.onHand == 7)
  let page ← IO.ofExcept <| (← resultValue state "stock-1").getObjValAs? Inventory.StockPage "page"
  check "aggregate query did not observe mutable stock" <|
    page.rows.any (fun row => row.item.sku == "SKU-A" && row.units == 5 && row.item.onHand == 7)
  let records ← journal session
  let initial := records[0]!
  let cfg ← IO.ofExcept <| initial.getObjValAs? Config "config"
  let task ← IO.ofExcept <| initial.getObjValAs? String "task"
  let replayed ← IO.ofExcept <| Recovery.replay (init session.toString cfg task Inventory.application)
    (records.toList.drop 1)
  check "independent journal replay differs from loaded state" (toJson replayed.state == toJson state)
  check "frozen seed was mutated instead of recording debits" (state.config.applicationData == toJson seed)

private def committedCrash (root : System.FilePath) (executable : String)
    (output : EventIO.Output) (mode : String) : IO Unit := do
  let session := root / s!"commit-{mode}"
  invoke executable #["start", mode, session.toString] (if mode == "uncertain" then 4 else 91)
  let prior ← checkpoint output session
  let interruptedRecords ← journal session
  let interruptedAtId := interruptedRecords.filter (fun record =>
    (record.getObjValAs? Nat "id").toOption == some prior.nextId)
  check "crash cutpoint unexpectedly wrote an outer completion" <|
    (interruptedAtId.filter (fun record =>
      (record.getObjValAs? String "kind").toOption == some "completion")).size ==
      (if mode == "uncertain" then 1 else 0)
  let interrupted ← load output session
  check "uncertain mutation was already treated as an authoritative success"
    ((results interrupted.cursor.state "reserve-1").isEmpty)
  let saved ← store session
  check "commit was not durable at the crash cutpoint" (saved.size == 2)
  let receipt ← IO.ofExcept <| saved[1]!.getObjValAs? Inventory.Reservation "receipt"
  check "store receipt does not bind the interrupted operation" <|
    receipt.operationId == prior.nextId && receipt.sessionId == prior.sessionId &&
    receipt.sku == "SKU-A" && receipt.units == 3 && receipt.before == 10 && receipt.remaining == 7
  let bytesBefore ← IO.FS.readBinFile (session / "inventory.jsonl")
  invoke executable #["resume", session.toString] 0
  verifyFinished output session
  check "reconciliation changed or appended the committed receipt"
    ((← IO.FS.readBinFile (session / "inventory.jsonl")) == bytesBefore)
  let records ← journal session
  let forOperation := records.filter (fun record =>
    (record.getObjValAs? Nat "id").toOption == some prior.nextId)
  check "mutation was re-dispatched instead of reconciled"
    ((forOperation.filter (fun record => (record.getObjValAs? String "kind").toOption == some "intent")).size == 1 &&
     (forOperation.filter (fun record => (record.getObjValAs? String "kind").toOption == some "resolution")).size == 1)
  let loaded ← load output session
  let options : Runner.Options := {session := session.toString, output}
  let context : ToolContext := {
    sessionPath := session.toString, sessionId := prior.sessionId, operationId := prior.nextId
    workspace := "", timeoutMs := 5000, outputBytes := 65536
    artifactDir := (session / "artifacts").toString, cancelPath := (session / "cancel").toString}
  -- Explicit adapter idempotency test: this is not a second engine dispatch.
  let repeated ← Runner.withLock options <| InventoryIO.runtime.execute loaded.cursor.state.config context
    ⟨"reserve-1", .reserve "SKU-A" 3⟩
  check "exact-key repeated adapter call did not return its prior receipt" <|
    match repeated with
    | .success result => (Inventory.encodeResult (.reserve "SKU-A" 3) result).compress ==
        (Inventory.encodeResult (.reserve "SKU-A" 3) receipt).compress
    | _ => false
  check "idempotent adapter call debited twice" ((← IO.FS.readBinFile (session / "inventory.jsonl")) == bytesBefore)
  if mode == "after" then
    Native.withFD (Native.openDir session.toString) fun directory =>
      Native.withFD (Native.openWriteAt directory "inventory.lock" false true 384) fun held => do
        check "contention fixture failed to acquire the owned inventory lock" (← Native.flock held true true)
        let started ← IO.monoMsNow
        let refused ← InventoryIO.runtime.execute loaded.cursor.state.config
          {context with operationId := loaded.cursor.state.nextId + 1}
          ⟨"contention-new-reservation", .reserve "SKU-A" 1⟩
        check "contended inventory lock did not fail promptly" ((← IO.monoMsNow) - started < 2000)
        check "contended inventory lock admitted a new reservation" <|
          match refused with
          | .uncertain message _ => message.contains "already held"
          | .failure message => message.contains "already held"
          | _ => false
        check "contended inventory operation appended a debit"
          ((← IO.FS.readBinFile (session / "inventory.jsonl")) == bytesBefore)
  let terminalBefore ← IO.FS.readBinFile (session / "journal.jsonl")
  invoke executable #["resume", session.toString] 0
  check "repeated terminal resume appended another result"
    ((← IO.FS.readBinFile (session / "journal.jsonl")) == terminalBefore)

private def missingReceipt (root : System.FilePath) (executable : String)
    (output : EventIO.Output) (afterCommit : Bool) : IO Unit := do
  let session := root / (if afterCommit then "lost-receipt" else "no-receipt")
  invoke executable #["start", if afterCommit then "after" else "before", session.toString]
    (if afterCommit then 91 else 92)
  let _ ← checkpoint output session
  if afterCommit then IO.FS.removeFile (session / "inventory.jsonl")
  let before ← IO.FS.readBinFile (session / "journal.jsonl")
  let storeBefore ← if afterCommit then pure none else
    some <$> IO.FS.readBinFile (session / "inventory.jsonl")
  for _ in [:2] do
    invoke executable #["resume", session.toString] 2
    check "missing receipt recovery rewrote outer evidence"
      ((← IO.FS.readBinFile (session / "journal.jsonl")) == before)
    match storeBefore with
    | none => check "missing ledger was recreated" (!(← (session / "inventory.jsonl").pathExists))
    | some bytes =>
      check "missing receipt was fabricated or reservation repeated"
        ((← IO.FS.readBinFile (session / "inventory.jsonl")) == bytes)
    let _ ← checkpoint output session

private def rewriteReceipt (session : System.FilePath) (record : Json) : IO Unit := do
  let header := (← store session)[0]!
  IO.FS.removeFile (session / "inventory.jsonl")
  JournalIO.append (session / "inventory.jsonl").toString header
  JournalIO.append (session / "inventory.jsonl").toString record

private def mismatch (root : System.FilePath) (executable : String) (output : EventIO.Output)
    (kind : String) : IO Unit := do
  let session := root / s!"mismatch-{kind}"
  invoke executable #["start", "after", session.toString] 91
  let prior ← checkpoint output session
  let entry := (← store session)[1]!
  let receipt ← IO.ofExcept (entry.getObjVal? "receipt")
  let changed := match kind with
    | "operation" => entry.mergeObj <| Json.mkObj [("receipt", receipt.mergeObj <|
        Json.mkObj [("operationId", toJson (prior.nextId + 1))])]
    | "session" => entry.mergeObj <| Json.mkObj [("receipt", receipt.mergeObj <|
        Json.mkObj [("sessionId", toJson (session.toString ++ "-different"))])]
    | "call" => entry.mergeObj (Json.mkObj [("callId", toJson "another-call")])
    | "sku" => entry.mergeObj <| Json.mkObj [("receipt", receipt.mergeObj <|
        Json.mkObj [("sku", toJson "SKU-B"), ("before", toJson (9 : Nat)), ("remaining", toJson (6 : Nat))])]
    | "units" => entry.mergeObj <| Json.mkObj [("receipt", receipt.mergeObj <|
        Json.mkObj [("units", toJson (4 : Nat)), ("remaining", toJson (6 : Nat))])]
    | "arithmetic" => entry.mergeObj <| Json.mkObj [("receipt", receipt.mergeObj <|
        Json.mkObj [("remaining", toJson (8 : Nat))])]
    | "seed" => entry.mergeObj <| Json.mkObj [("seedSha256", toJson (String.ofList (List.replicate 64 '0')))]
    | _ => entry
  rewriteReceipt session changed
  let outerBefore ← IO.FS.readBinFile (session / "journal.jsonl")
  let storeBefore ← IO.FS.readBinFile (session / "inventory.jsonl")
  invoke executable #["resume", session.toString] 2
  check s!"{kind} mismatch advanced or rewrote evidence" <|
    (← IO.FS.readBinFile (session / "journal.jsonl")) == outerBefore &&
    (← IO.FS.readBinFile (session / "inventory.jsonl")) == storeBefore
  let _ ← checkpoint output session

private def incompleteTail (root : System.FilePath) (executable : String)
    (output : EventIO.Output) : IO Unit := do
  let session := root / "incomplete-receipt-tail"
  invoke executable #["start", "after", session.toString] 91
  let _ ← checkpoint output session
  let path := session / "inventory.jsonl"
  let original ← IO.FS.readBinFile path
  let interrupted := original ++ "{\"incomplete\":".toUTF8
  IO.FS.writeBinFile path interrupted
  let outerBefore ← IO.FS.readBinFile (session / "journal.jsonl")
  invoke executable #["resume", session.toString] 2
  check "incomplete receipt tail was repaired or ignored"
    ((← IO.FS.readBinFile path) == interrupted &&
      (← IO.FS.readBinFile (session / "journal.jsonl")) == outerBefore)

private def noDebit (root : System.FilePath) (executable : String) (output : EventIO.Output)
    (mode : String) : IO Unit := do
  let session := root / mode
  invoke executable #["start", mode, session.toString] 0
  let loaded ← load output session
  let state := loaded.cursor.state
  check s!"{mode}: expected normal scripted completion" (loaded.cursor.terminal && isFinal state)
  let entries ← store session
  check s!"{mode}: expected only the exclusive startup header, no debit" <|
    entries.size == 1 && (entries[0]!.getObjValAs? String "kind").toOption == some "inventory"
  let reserveResults := results state "reserve-1"
  check s!"{mode}: reservation did not produce exactly one explicit error"
    (reserveResults.size == 1 && (reserveResults[0]!.getObjValAs? Bool "is_error").toOption == some true)
  if mode == "deny" then
    check "global deny dispatched a query or reservation" (state.toolDispatches == 0)
  else
    check s!"{mode}: error refunded a dispatch" (state.toolDispatches == 3)
  if mode == "insufficient" then
    let found ← IO.ofExcept <| (← resultValue state "lookup-1").getObjValAs? Inventory.Item "item"
    check "insufficient stock changed quantity" (found.onHand == 10)

def run (root : System.FilePath) (executable : String) (output : EventIO.Output) : IO Unit := do
  committedCrash root executable output "after"
  committedCrash root executable output "uncertain"
  missingReceipt root executable output false
  missingReceipt root executable output true
  for kind in #["operation", "session", "call", "sku", "units", "arithmetic", "seed"] do
    mismatch root executable output kind
  incompleteTail root executable output
  noDebit root executable output "deny"
  noDebit root executable output "insufficient"
  noDebit root executable output "output-bound"
  IO.println "inventory reservation IO: 16 crash/reconciliation/identity/permission/bounds/lock cases passed"

end Tests.InventoryRecovery

def main (arguments : List String) : IO UInt32 := do
  Harness.Native.installSignals
  match arguments with
  | "--child" :: childArguments =>
    try Tests.InventoryRecovery.child childArguments
    catch error => IO.eprintln s!"inventory-recovery child: {error}"; pure 2
  | [] =>
    let executable ← IO.appPath
    let root := System.FilePath.mk s!"/tmp/lean-harness-inventory-recovery-{← IO.monoNanosNow}"
    Harness.Native.mkdir root.toString 448
    let output ← Harness.EventIO.create
    try
      Tests.InventoryRecovery.run root executable.toString output
      return 0
    finally
      Harness.EventIO.close output
      IO.FS.removeDirAll root
  | _ => IO.eprintln "usage: inventory_recovery_contracts"; pure 2
