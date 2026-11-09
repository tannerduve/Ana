import Harness.Applications.Inventory
import Harness.Adapter.ApplicationIO
import Harness.Adapter.JournalIO

/-! Session-local inventory state. A single framed receipt is both the stock debit
and its idempotency evidence. Reads replay validated receipts from the frozen seed;
there is no separately updated stock file that can diverge from the receipt log.
The Runner owns the session lock. A second nonblocking lock also serializes direct
adapter callers; session-directory names are trusted to remain stable while held. -/
namespace Harness.InventoryStoreIO
open Lean Inventory

def maximumBytes : Nat := 4 * 1024 * 1024
def maximumReceipts : Nat := 4096

structure Entry where
  callId : String
  receipt : Reservation
  deriving Repr

structure Snapshot where
  data : Dataset
  seedSha256 : String
  receipts : Array Entry := #[]
  bytes : Nat := 0
  deriving Repr

def ledgerPath (context : ApplicationIO.OperationContext) : String :=
  context.session ++ "/inventory.jsonl"

def operationContext (context : ToolContext) : ApplicationIO.OperationContext :=
  {session := context.sessionPath, sessionId := context.sessionId, operationId := context.operationId}

def validateIdentity (context : ApplicationIO.OperationContext) : IO Unit := do
  let canonical ← ApplicationIO.canonicalSessionPath context.session
  unless canonical == context.session && context.sessionId == canonical &&
      validReservationKey ⟨context.sessionId, context.operationId⟩ do
    throw <| IO.userError "inventory operation requires its frozen canonical session identity"
  Native.withFD (Native.openDir canonical) fun _ => pure ()

private def validCallId (value : String) : Bool :=
  !value.isEmpty && value.utf8ByteSize ≤ 4096 && !value.contains '\x00'

private def sameFile (a b : Native.FileInfo) : Bool :=
  a.device == b.device && a.inode == b.inode && a.kind == b.kind &&
    a.links == b.links && a.size == b.size

private def checkedInfo (directory : Native.FD) : IO Native.FileInfo := do
  let info ← Native.statAt directory "inventory.jsonl"
  unless info.kind == 4 || (info.kind == 1 && info.links == 1 && info.size ≤ maximumBytes) do
    throw <| IO.userError "inventory ledger must be a singly-linked regular file of at most 4 MiB"
  return info

def encodeEntry (seedSha256 : String) (entry : Entry) : Json :=
  Json.mkObj [("version", toJson (1 : Nat)), ("seedSha256", toJson seedSha256),
    ("callId", toJson entry.callId), ("receipt", toJson entry.receipt)]

/-- Read only; callers that race an update must hold the inventory/session lock.
The initialized header is mandatory: a lost ledger must never reset stock. -/
def read (config : Config) (context : ApplicationIO.OperationContext) : IO Snapshot := do
  validateIdentity context
  let seed ← IO.ofExcept <| validateData config.applicationData
  let seedSha256 ← Native.sha256 (toJson seed).compress.toUTF8
  Native.withFD (Native.openDir context.session) fun directory => do
    let before ← checkedInfo directory
    if before.kind == 4 then throw <| IO.userError "inventory ledger is missing; automatic reset refused"
    let journal ← JournalIO.read (ledgerPath context)
    let after ← checkedInfo directory
    unless sameFile before after do throw <| IO.userError "inventory ledger changed while reading"
    if journal.interrupted then throw <| IO.userError "inventory ledger has an incomplete tail; automatic recovery refused"
    if journal.records.size > maximumReceipts + 1 then throw <| IO.userError "inventory receipt limit exceeded"
    let some header := journal.records[0]? | throw <| IO.userError "inventory ledger has no initialized header"
    IO.ofExcept <| exactFields header ["kind", "version", "applicationVersion", "seedSha256", "sessionId"]
    unless (header.getObjValAs? String "kind").toOption == some "inventory" &&
        (header.getObjValAs? Nat "version").toOption == some 1 &&
        (header.getObjValAs? Nat "applicationVersion").toOption == some Inventory.application.version &&
        (header.getObjValAs? String "seedSha256").toOption == some seedSha256 &&
        (header.getObjValAs? String "sessionId").toOption == some context.sessionId do
      throw <| IO.userError "inventory header differs from the frozen application, seed or session"
    let mut snapshot : Snapshot := {data := seed, seedSha256, bytes := after.size}
    let mut lastOperation : Option Nat := none
    let mut callIds : List String := []
    for record in journal.records.toList.drop 1 do
      IO.ofExcept <| exactFields record ["version", "seedSha256", "callId", "receipt"]
      unless (record.getObjValAs? Nat "version").toOption == some 1 &&
          (record.getObjValAs? String "seedSha256").toOption == some seedSha256 do
        throw <| IO.userError "inventory receipt version or frozen seed differs"
      let callId ← IO.ofExcept <| record.getObjValAs? String "callId"
      let receipt ← IO.ofExcept <| reservationFromJson (← IO.ofExcept <| record.getObjVal? "receipt")
      unless validCallId callId && !callIds.contains callId && receipt.sessionId == context.sessionId &&
          !(lastOperation.any (receipt.operationId ≤ ·)) do
        throw <| IO.userError "duplicate, out-of-order or foreign inventory receipt identity"
      let data ← IO.ofExcept <| applyReservation snapshot.data receipt
      snapshot := {snapshot with data, receipts := snapshot.receipts.push {callId, receipt}}
      lastOperation := some receipt.operationId
      callIds := callId :: callIds
    return snapshot

private def withLock (context : ApplicationIO.OperationContext) (body : IO α) : IO α := do
  validateIdentity context
  Native.withFD (Native.openDir context.session) fun directory =>
    Native.withFD (Native.openWriteAt directory "inventory.lock" false true 384) fun lock => do
      let opened ← Native.stat lock
      let linked ← Native.statAt directory "inventory.lock"
      unless opened.kind == 1 && opened.links == 1 && sameFile opened linked do
        throw <| IO.userError "inventory lock must be a stable singly-linked regular file"
      unless ← Native.flock lock true true do throw <| IO.userError "inventory ledger is already held"
      Native.sync lock
      Native.sync directory
      body

/-- Called only after exclusive session creation and before its initial record.
An interrupted initialization leaves evidence and is never silently recreated. -/
def initializeSession (session : String) (config : Config) : IO Unit := do
  let context : ApplicationIO.OperationContext := {session, sessionId := session, operationId := 0}
  withLock context do
    let seed ← IO.ofExcept <| validateData config.applicationData
    let seedSha256 ← Native.sha256 (toJson seed).compress.toUTF8
    Native.withFD (Native.openDir session) fun directory =>
      Native.withFD (Native.openWriteAt directory "inventory.jsonl" true false 384) fun fd => do
        Native.sync fd
        Native.sync directory
    JournalIO.append (ledgerPath context) <| Json.mkObj [
      ("kind", toJson "inventory"), ("version", toJson (1 : Nat)),
      ("applicationVersion", toJson Inventory.application.version),
      ("seedSha256", toJson seedSha256), ("sessionId", toJson session)]
    let _ ← read config context
    pure ()

/-- A receipt visible after an earlier failed sync is not yet durability evidence.
Reconfirm both the existing file and its parent before returning it as settled. -/
private def confirmDurable (context : ApplicationIO.OperationContext) (expectedBytes : Nat) : IO Unit :=
  Native.withFD (Native.openDir context.session) fun directory => do
    let linked ← checkedInfo directory
    unless linked.kind == 1 && linked.size == expectedBytes do
      throw <| IO.userError "inventory receipt disappeared or changed before durability confirmation"
    Native.withFD (Native.openReadAt directory "inventory.jsonl") fun fd => do
      unless sameFile linked (← Native.stat fd) do
        throw <| IO.userError "inventory receipt file identity changed"
      Native.sync fd
      Native.sync directory
      unless sameFile linked (← checkedInfo directory) do
        throw <| IO.userError "inventory ledger changed during durability confirmation"

def findReceipt (snapshot : Snapshot) (context : ApplicationIO.OperationContext)
    (callId sku : String) (units : Nat) : Except String (Option Reservation) := do
  unless validCallId callId do throw "invalid inventory call identity"
  match snapshot.receipts.find? (fun entry => entry.receipt.operationId == context.operationId) with
  | some entry =>
    unless entry.callId == callId && entry.receipt.sessionId == context.sessionId &&
        entry.receipt.sku == sku && entry.receipt.units == units do
      throw "inventory operation identity was already used with different arguments"
    return some entry.receipt
  | none =>
    if snapshot.receipts.any (fun entry => entry.callId == callId || entry.receipt.operationId ≥ context.operationId) then
      throw "inventory call identity or operation order conflicts with the ledger"
    return none

/-- Only this function appends a stock mutation. Expected domain failures and
output limits are checked before append; any commit exception remains uncertain. -/
def reserve (config : Config) (context : ApplicationIO.OperationContext)
    (callId sku : String) (units outputBytes : Nat)
    (beforeCommit : IO (Option (ToolObservation Reservation))) : IO (ToolObservation Reservation) :=
  withLock context do
    let snapshot ← read config context
    match findReceipt snapshot context callId sku units with
    | .error message => return .uncertain message
    | .ok (some receipt) =>
      confirmDurable context snapshot.bytes
      if (render (.reserve sku units) receipt).text.utf8ByteSize > outputBytes then
        return .uncertain "recorded reservation receipt exceeds output limit" (some receipt)
      return .success receipt
    | .ok none => pure ()
    let (_, receipt) ← match Inventory.reserve snapshot.data ⟨context.sessionId, context.operationId⟩ (.reserve sku units) with
      | .error message => return .failure message
      | .ok value => pure value
    if (render (.reserve sku units) receipt).text.utf8ByteSize > outputBytes then
      return .failure "Inventory result exceeds output limit; no reservation was committed."
    let record := encodeEntry snapshot.seedSha256 {callId, receipt}
    if snapshot.receipts.size ≥ maximumReceipts ||
        snapshot.bytes + record.compress.utf8ByteSize + 512 > maximumBytes then
      return .failure "Inventory ledger capacity exceeded; no reservation was committed."
    if let some stopped ← beforeCommit then return stopped
    try
      JournalIO.append (ledgerPath context) record
      let saved ← read config context
      unless (findReceipt saved context callId sku units).toOption == some (some receipt) do
        throw <| IO.userError "committed inventory receipt did not validate"
      confirmDurable context saved.bytes
      return .success receipt
    catch error =>
      return .uncertain s!"inventory reservation commit could not be confirmed: {error}"

/-- Return only an exact durable receipt; absence never authorizes a retry. -/
def reconcile (config : Config) (context : ApplicationIO.OperationContext)
    (call : Call Inventory.application) (witness : Option Witness) : IO Reservation :=
  withLock context do
    let some witness := witness | throw <| IO.userError "unresolved reservation has no saved witness"
    IO.ofExcept <| Inventory.validateWitness call.operation witness
    unless witness.sessionId == context.sessionId && witness.operationId == context.operationId do
      throw <| IO.userError "inventory witness differs from the saved operation identity"
    let snapshot ← read config context
    let some receipt ← IO.ofExcept <| findReceipt snapshot context call.id witness.sku witness.units
      | throw <| IO.userError "no durable inventory receipt; automatic reservation retry refused"
    let _ ← IO.ofExcept <| Inventory.resolve call.operation (some witness) receipt
    confirmDurable context snapshot.bytes
    return receipt

/-- Queries observe the same validated ledger while excluding a concurrent debit. -/
def query (config : Config) (context : ApplicationIO.OperationContext) (op : Operation) : IO (Except String (Result op)) :=
  withLock context do
    let snapshot ← read config context
    pure <| Inventory.query snapshot.data op

end Harness.InventoryStoreIO
