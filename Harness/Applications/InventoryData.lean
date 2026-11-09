import Lean

/-!
Validated local inventory data, queries and pure reservation updates. The initial dataset is
session input; the IO interpreter durably records session-local reservations. This is not a
warehouse service. No model operation accepts a filesystem path or an operation identity.
-/
namespace Harness.Inventory
open Lean

structure Item where
  sku : String
  name : String
  warehouse : String
  onHand : Nat
  reorderPoint : Nat
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure Dataset where
  version : Nat
  items : Array Item
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure ReorderRow where
  item : Item
  units : Nat
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure StockPage where
  rows : Array ReorderRow
  matched : Nat
  offset : Nat
  nextOffset : Option Nat
  truncated : Bool
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure WarehouseSummary where
  warehouse : String
  itemCount : Nat
  lowStockCount : Nat
  shortfallUnits : Nat
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

/-- Supplied by the runner, never by model arguments. -/
structure ReservationKey where
  sessionId : String
  operationId : Nat
  deriving Repr, BEq, DecidableEq, ToJson

structure Reservation where
  sessionId : String
  operationId : Nat
  sku : String
  units : Nat
  before : Nat
  remaining : Nat
  deriving Repr, BEq, DecidableEq, ToJson

structure Witness where
  sessionId : String
  operationId : Nat
  sku : String
  units : Nat
  deriving Repr, BEq, DecidableEq, ToJson

abbrev Resolution := Reservation

/-- Strict field sets are shared by the input and result codecs. -/
def exactFields (json : Json) (names : List String) : Except String Unit := do
  let fields ← json.getObj?
  unless fields.size == names.length && fields.toList.all (fun pair => names.contains pair.1) do
    throw "unexpected or missing inventory fields"

def validIdentifier (value : String) : Bool :=
  !value.isEmpty && value.utf8ByteSize ≤ 64 &&
    value.toList.all (fun c => c.isAlphanum && c.toNat < 128 || c == '-' || c == '_')

def validReservationKey (key : ReservationKey) : Bool :=
  !key.sessionId.isEmpty && key.sessionId.utf8ByteSize ≤ 4096 &&
    key.sessionId.toList.all (fun c => c.toNat ≥ 32 && c.toNat != 127) &&
    key.operationId ≤ 18446744073709551615

def validReservationArgs (sku : String) (units : Nat) : Bool :=
  validIdentifier sku && 0 < units && units ≤ 1000000

/-- Arithmetic and identity validation applies even to directly constructed typed receipts. -/
def validateReservation (receipt : Reservation) : Except String Unit := do
  unless validReservationKey ⟨receipt.sessionId, receipt.operationId⟩ &&
      validReservationArgs receipt.sku receipt.units do
    throw "invalid reservation identity or arguments"
  unless receipt.before ≤ 1000000 && receipt.units ≤ receipt.before &&
      receipt.remaining + receipt.units == receipt.before do
    throw "invalid reservation stock arithmetic"

def reservationFromJson (json : Json) : Except String Reservation := do
  exactFields json ["sessionId", "operationId", "sku", "units", "before", "remaining"]
  let receipt : Reservation := {
    sessionId := ← json.getObjValAs? String "sessionId"
    operationId := ← json.getObjValAs? Nat "operationId"
    sku := ← json.getObjValAs? String "sku"
    units := ← json.getObjValAs? Nat "units"
    before := ← json.getObjValAs? Nat "before"
    remaining := ← json.getObjValAs? Nat "remaining"}
  validateReservation receipt
  return receipt

instance : FromJson Reservation := ⟨reservationFromJson⟩

def witnessFromJson (json : Json) : Except String Witness := do
  exactFields json ["sessionId", "operationId", "sku", "units"]
  let witness : Witness := {
    sessionId := ← json.getObjValAs? String "sessionId"
    operationId := ← json.getObjValAs? Nat "operationId"
    sku := ← json.getObjValAs? String "sku"
    units := ← json.getObjValAs? Nat "units"}
  unless validReservationKey ⟨witness.sessionId, witness.operationId⟩ &&
      validReservationArgs witness.sku witness.units do
    throw "invalid reservation witness"
  return witness

instance : FromJson Witness := ⟨witnessFromJson⟩

def validateItem (item : Item) : Except String Unit := do
  unless validIdentifier item.sku && validIdentifier item.warehouse do
    throw "inventory SKU and warehouse must be 1..64 ASCII letters, digits, '_' or '-'"
  unless !item.name.trimAscii.toString.isEmpty && item.name.utf8ByteSize ≤ 256 &&
      item.name.toList.all (fun c => c.toNat ≥ 32 && c.toNat != 127) do
    throw "inventory name must be nonempty bounded text without control characters"
  unless item.onHand ≤ 1000000 && item.reorderPoint ≤ 1000000 do
    throw "inventory quantities must be at most 1000000"

def itemFromJson (json : Json) : Except String Item := do
  exactFields json ["sku", "name", "warehouse", "onHand", "reorderPoint"]
  let item : Item ← fromJson? json
  validateItem item
  return item

/-- Admit at most 512 unique SKUs across 64 warehouses; preserve input order. -/
def validateData (json : Json) : Except String Dataset := do
  unless json.compress.utf8ByteSize ≤ 1024 * 1024 do throw "inventory dataset exceeds 1 MiB"
  exactFields json ["version", "items"]
  let version ← json.getObjValAs? Nat "version"
  unless version == 1 do throw "unsupported inventory dataset version"
  let entries ← (← json.getObjVal? "items").getArr?
  unless entries.size ≤ 512 do throw "inventory dataset exceeds 512 items"
  let mut items := #[]
  let mut skus : List String := []
  let mut warehouses : List String := []
  for entry in entries do
    let item ← itemFromJson entry
    if skus.contains item.sku then throw "duplicate inventory SKU"
    skus := item.sku :: skus
    if !warehouses.contains item.warehouse then warehouses := item.warehouse :: warehouses
    if warehouses.length > 64 then throw "inventory dataset exceeds 64 warehouses"
    items := items.push item
  return {version, items}

inductive Operation where
  | lookup (sku : String)
  | lowStock (warehouse : String) (offset limit : Nat)
  | warehouseTotals
  | reserve (sku : String) (units : Nat)
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

/-- These are distinct Lean types, not one JSON/string result type behind every call. -/
abbrev Result : Operation → Type
  | .lookup _ => Option Item
  | .lowStock _ _ _ => StockPage
  | .warehouseTotals => Array WarehouseSummary
  | .reserve _ _ => Reservation

/-- A pure, all-or-error debit. The caller must journal the returned update before
reporting success; this function alone performs no mutation or durable commit. -/
def reserve (data : Dataset) (key : ReservationKey) (op : Operation) :
    Except String (Dataset × Reservation) := do
  let .reserve sku units := op | throw "reservation update requires the reserve operation"
  unless validReservationKey key && validReservationArgs sku units do
    throw "invalid reservation identity or arguments"
  let _ ← validateData (toJson data)
  let some item := data.items.find? (fun item => item.sku == sku) | throw "unknown reservation SKU"
  unless units ≤ item.onHand do throw "insufficient inventory stock"
  let receipt : Reservation := {
    sessionId := key.sessionId, operationId := key.operationId, sku, units,
    before := item.onHand, remaining := item.onHand - units}
  let items := data.items.map fun row =>
    if row.sku == sku then {row with onHand := receipt.remaining} else row
  return ({data with items}, receipt)

/-- Replaying a receipt recomputes its expected debit from current stock. The IO
ledger additionally enforces unique keys; this function never invents a receipt. -/
def applyReservation (data : Dataset) (receipt : Reservation) : Except String Dataset := do
  validateReservation receipt
  let (next, expected) ← reserve data ⟨receipt.sessionId, receipt.operationId⟩
    (.reserve receipt.sku receipt.units)
  unless expected == receipt do throw "reservation receipt does not match current stock"
  return next

def shortfall (item : Item) : Nat := item.reorderPoint - item.onHand

/-- Compute against the supplied validated stock, never the model's proposed answer.
Reservations require the durable IO path and cannot use the read-only query path. -/
def query (data : Dataset) : (op : Operation) → Except String (Result op)
  | .lookup sku => do
    unless validIdentifier sku do throw "invalid SKU"
    return data.items.find? (fun item => item.sku == sku)
  | .lowStock warehouse offset limit => do
    unless validIdentifier warehouse && offset ≤ 512 && 0 < limit && limit ≤ 100 do
      throw "invalid warehouse, offset (0..512), or limit (1..100)"
    unless data.items.any (fun item => item.warehouse == warehouse) do
      throw "unknown warehouse"
    let matching := data.items.filter (fun item => item.warehouse == warehouse && shortfall item > 0)
    let rows := ((matching.toList.drop offset).take limit).toArray.map
      (fun item => ({item, units := shortfall item} : ReorderRow))
    let more := offset + rows.size < matching.size
    return {
      rows
      matched := matching.size
      offset
      nextOffset := if more then some (offset + rows.size) else none
      truncated := more}
  | .warehouseTotals => do
    let warehouses := data.items.foldl (fun acc item =>
      if acc.contains item.warehouse then acc else acc.push item.warehouse) (#[] : Array String)
    return warehouses.map fun warehouse =>
      let items := data.items.filter (fun item => item.warehouse == warehouse)
      {warehouse, itemCount := items.size,
       lowStockCount := (items.filter (fun item => shortfall item > 0)).size,
       shortfallUnits := items.foldl (fun total item => total + shortfall item) 0}
  | .reserve _ _ => .error "reservation requires the durable inventory interpreter"

end Harness.Inventory
