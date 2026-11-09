import Harness.Applications.Inventory
import Harness.Adapter.ApplicationIO
import Harness.Adapter.Native
import Harness.Applications.InventoryStoreIO

/-! IO boundary for inventory: replay the session ledger, then query or reserve stock.
The shared runner owns cancellation, permissions, budgets, journal durability and recovery.
No operation reads the original input file or executes another program. Reservation
success requires a durable receipt; cancellation after commit retains uncertainty
and the receipt, never an ordinary failure claiming that no mutation happened. -/
namespace Harness.InventoryIO
open Lean

def prepareConfig (config : Config) : IO Config := do
  unless config.workspace.isEmpty && config.toolchainRoots.isEmpty &&
      config.executionProfile == .host && config.commands == .ask do
    throw <| IO.userError "inventory has no workspace, process profile or command policy; use toolPolicy for queries"
  let data ← IO.ofExcept (Inventory.validateData config.applicationData)
  return {config with applicationData := toJson data}

private def validateConfig (session : String) (config : Config) : IO Unit := do
  let _ ← prepareConfig config
  if ← (System.FilePath.mk session).pathExists then
    let _ ← InventoryStoreIO.read config {session, sessionId := session, operationId := 0}
    pure ()
  pure ()

private def stopped {α : Type} (context : ToolContext) (started : Nat) :
    IO (Option (ToolObservation α)) := do
  if ← Native.isCancelled then return some (.interrupted "inventory operation cancelled")
  if !context.cancelPath.isEmpty && (← (System.FilePath.mk context.cancelPath).pathExists) then
    return some (.interrupted "inventory operation cancelled")
  let now ← IO.monoMsNow
  if context.invocationDeadlineMs.any (now ≥ ·) then
    return some (.interrupted "invocation deadline expired during inventory operation")
  if now - started ≥ context.timeoutMs then
    return some (.failure "Inventory operation time limit exceeded before commit; no stock was changed.")
  return none

private def prepare (_ : Config) (context : ApplicationIO.OperationContext)
    (call : Call Inventory.application) : IO (Option Inventory.Witness) := do
  match call.operation with
  | .reserve sku units =>
    InventoryStoreIO.validateIdentity context
    let witness : Inventory.Witness := {
      sessionId := context.sessionId, operationId := context.operationId, sku, units}
    IO.ofExcept <| Inventory.validateWitness call.operation witness
    return some witness
  | _ => return none

private def executeOperation (config : Config) (context : ToolContext) (started : Nat)
    (callId : String) : (op : Inventory.Operation) → IO (ToolObservation (Inventory.Result op))
  | .reserve sku units => do
    let outcome ← InventoryStoreIO.reserve config (InventoryStoreIO.operationContext context)
      callId sku units context.outputBytes (stopped context started)
    match outcome with
    | .success receipt =>
      if let some interrupted ← stopped (α := Inventory.Reservation) context started then
        match interrupted with
        | .interrupted message _ =>
          return .interrupted (message ++ "; reservation receipt was committed") (some receipt)
        | _ =>
          return .uncertain "inventory operation deadline observed after reservation commit" (some receipt)
      return .success receipt
    | other => return other
  | op => do
    let result ← InventoryStoreIO.query config (InventoryStoreIO.operationContext context) op
    let outcome := match result with
      | .ok result =>
        if (Inventory.render op result).text.utf8ByteSize ≤ context.outputBytes then .success result
        else .failure "Inventory result exceeds output limit; request a smaller page."
      | .error message => .failure message
    if let some observation ← stopped context started then return observation
    return outcome

def runtime : ApplicationIO.Runtime Inventory.application where
  prepareConfig := prepareConfig
  initializeSession := InventoryStoreIO.initializeSession
  validate := validateConfig
  validateIdentity := validateConfig
  prepare := prepare
  reconcile := InventoryStoreIO.reconcile
  execute := fun config context call => do
    let started ← IO.monoMsNow
    if let some observation ← stopped context started then return observation
    try executeOperation config context started call.id call.operation
    catch error => return .uncertain s!"inventory ledger could not establish the operation outcome: {error}"

end Harness.InventoryIO
