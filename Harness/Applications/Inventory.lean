import Harness.Core.Application
import Harness.Applications.InventoryValidity

/-!
A session-local inventory application for the shared harness. Typed results survive execution,
journaling and replay; JSON is only their checked boundary representation. The frozen seed in
`Config.applicationData` and durable reservation receipts determine current stock.
-/
namespace Harness.Inventory
open Lean

def name : Operation → String
  | .lookup _ => "lookup"
  | .lowStock _ _ _ => "low_stock"
  | .warehouseTotals => "warehouse_totals"
  | .reserve _ _ => "reserve"

def args : Operation → Json
  | .lookup sku => Json.mkObj [("sku", toJson sku)]
  | .lowStock warehouse offset limit => Json.mkObj [("warehouse", toJson warehouse),
      ("offset", toJson offset), ("limit", toJson limit)]
  | .warehouseTotals => Json.mkObj []
  | .reserve sku units => Json.mkObj [("sku", toJson sku), ("units", toJson units)]

def decode (raw : RawCall) : Except String Operation := do
  match raw.name with
  | "lookup" =>
    exactFields raw.input ["sku"]
    let sku ← raw.input.getObjValAs? String "sku"
    unless validIdentifier sku do throw "invalid inventory SKU"
    return .lookup sku
  | "low_stock" =>
    let fields ← raw.input.getObj?
    unless fields.toList.all (fun pair => ["warehouse", "offset", "limit"].contains pair.1) do
      throw "unknown inventory argument"
    let warehouse ← raw.input.getObjValAs? String "warehouse"
    let offset ← match raw.input.getObjVal? "offset" with
      | .ok value => fromJson? value
      | .error _ => pure (0 : Nat)
    let limit ← match raw.input.getObjVal? "limit" with
      | .ok value => fromJson? value
      | .error _ => pure (50 : Nat)
    unless validIdentifier warehouse && offset ≤ 512 && 0 < limit && limit ≤ 100 do
      throw "invalid warehouse, offset (0..512), or limit (1..100)"
    return .lowStock warehouse offset limit
  | "warehouse_totals" =>
    exactFields raw.input []
    return .warehouseTotals
  | "reserve" =>
    exactFields raw.input ["sku", "units"]
    let sku ← raw.input.getObjValAs? String "sku"
    let units ← raw.input.getObjValAs? Nat "units"
    unless validReservationArgs sku units do throw "invalid reservation SKU or units (1..1000000)"
    return .reserve sku units
  | _ => throw s!"unknown inventory tool: {raw.name}"

def encodeResult : (op : Operation) → Result op → Json
  | .lookup _, item => Json.mkObj [("kind", toJson "lookup"), ("item", toJson (α := Option Item) item)]
  | .lowStock _ _ _, page => Json.mkObj [("kind", toJson "low_stock"), ("page", toJson (α := StockPage) page)]
  | .warehouseTotals, rows => Json.mkObj [("kind", toJson "warehouse_totals"), ("warehouses", toJson (α := Array WarehouseSummary) rows)]
  | .reserve _ _, receipt => Json.mkObj [("kind", toJson "reserve"), ("reservation", toJson receipt)]

private def checkKind (json : Json) (kind : String) (field : String) : Except String Json := do
  exactFields json ["kind", field]
  unless (← json.getObjValAs? String "kind") == kind do throw "inventory result belongs to another operation"
  json.getObjVal? field

/-- Strict shape readers do not silently ignore extra fields in nested records. -/
def rowFromJson (json : Json) : Except String ReorderRow := do
  exactFields json ["item", "units"]
  let item ← itemFromJson (← json.getObjVal? "item")
  let units ← json.getObjValAs? Nat "units"
  return {item, units}

def pageFromJson (json : Json) : Except String StockPage := do
  exactFields json ["rows", "matched", "offset", "nextOffset", "truncated"]
  let rows ← (← json.getObjVal? "rows").getArr?
  unless rows.size ≤ 100 do throw "too many low-stock rows"
  let rows ← rows.mapM rowFromJson
  let matched ← json.getObjValAs? Nat "matched"
  let offset ← json.getObjValAs? Nat "offset"
  let nextOffset ← json.getObjValAs? (Option Nat) "nextOffset"
  let truncated ← json.getObjValAs? Bool "truncated"
  return {rows, matched, offset, nextOffset, truncated}

def summaryFromJson (json : Json) : Except String WarehouseSummary := do
  exactFields json ["warehouse", "itemCount", "lowStockCount", "shortfallUnits"]
  fromJson? json

/-- Parse the exact tagged shape, then check independently defined domain bounds and correlations.
The extra-field policy is unchanged; validity never means success of an encode/decode roundtrip. -/
def decodeResult : (op : Operation) → Json → Except String (Result op)
  | .lookup sku, json => do
    let item ← checkKind json "lookup" "item"
    let value ← if item.isNull then pure none else some <$> itemFromJson item
    unless validResult (.lookup sku) value do throw "lookup result has invalid fields or a different SKU"
    return value
  | .lowStock warehouse offset limit, json => do
    let page ← pageFromJson (← checkKind json "low_stock" "page")
    unless validResult (.lowStock warehouse offset limit) page do
      throw "invalid low-stock result bounds, continuation, warehouse, shortfall, or duplicate SKU"
    return page
  | .warehouseTotals, json => do
    let rows ← (← checkKind json "warehouse_totals" "warehouses").getArr?
    unless rows.size ≤ 64 do throw "too many warehouse summaries"
    let rows ← rows.mapM summaryFromJson
    unless validResult .warehouseTotals rows do throw "invalid or duplicate warehouse summaries"
    return rows
  | .reserve sku units, json => do
    let receipt ← reservationFromJson (← checkKind json "reserve" "reservation")
    unless validResult (.reserve sku units) receipt do
      throw "reservation result has invalid fields or belongs to different arguments"
    return receipt

/-- Recovery witnesses bind only runner-owned identity and the exact operation arguments. -/
def validateWitness (op : Operation) (witness : Witness) : Except String Unit := do
  let .reserve sku units := op | throw "inventory query has no mutation witness"
  unless validReservationKey ⟨witness.sessionId, witness.operationId⟩ &&
      validReservationArgs sku units && witness.sku == sku && witness.units == units do
    throw "reservation witness does not match operation"

/-- Only a matching durable receipt can settle a reservation. The IO interpreter
must obtain that receipt from its validated session ledger, not an operator claim. -/
def resolve : (op : Operation) → Option Witness → Resolution → Except String (Settled (Result op))
  | .reserve sku units, witness, receipt => do
    let some witness := witness | throw "reservation resolution requires its saved witness"
    validateWitness (.reserve sku units) witness
    validateReservation receipt
    unless receipt.sessionId == witness.sessionId && receipt.operationId == witness.operationId &&
        receipt.sku == witness.sku && receipt.units == witness.units do
      throw "reservation receipt does not match saved witness"
    return .success receipt
  | _, _, _ => .error "inventory queries have no reservation resolution"

private def property (kind : String) (description : String) : Json :=
  Json.mkObj [("type", toJson kind), ("description", toJson description)]

private def schema (toolName description : String) (fields : List (String × Json))
    (required : List String) : Json :=
  Json.mkObj [("name", toJson toolName), ("description", toJson description),
    ("input_schema", Json.mkObj [("type", toJson "object"), ("properties", Json.mkObj fields),
      ("required", toJson required), ("additionalProperties", toJson false)])]

def toolSchemas : Array Json := #[
  schema "warehouse_totals"
    "Summarize every warehouse in current session-local stock: item count, number below their reorder point, and replenishment units. Results follow seed order. This reads the session reservation ledger, not an external warehouse service."
    [] [],
  schema "low_stock"
    "List items below their reorder point in one warehouse, with replenishment units equal to reorderPoint minus onHand. Input order is preserved. Follow nextOffset with the same warehouse to retrieve later pages; null means complete. A missing warehouse is an error."
    [("warehouse", property "string" "Exact warehouse identifier from warehouse_totals"),
     ("offset", Json.mkObj [("type", toJson "integer"), ("minimum", toJson (0 : Nat)),
       ("maximum", toJson (512 : Nat)), ("description", toJson "Zero-based matching-row offset; default 0")]),
     ("limit", Json.mkObj [("type", toJson "integer"), ("minimum", toJson (1 : Nat)),
       ("maximum", toJson (100 : Nat)), ("description", toJson "Maximum returned rows; default 50")])]
    ["warehouse"],
  schema "lookup"
    "Look up one unique SKU in current session-local stock. Returns its item or null if absent. No arbitrary paths or queries are accepted."
    [("sku", property "string" "Exact SKU identifier")]
    ["sku"],
  schema "reserve"
    "Reserve a positive quantity of one SKU in this session's inventory. Commits a receipt and decreases local stock only if enough remains; no external warehouse is modified. Runner-owned identity makes recovery of this same interrupted operation idempotent. A new call is a new reservation."
    [("sku", property "string" "Exact SKU identifier"),
     ("units", Json.mkObj [("type", toJson "integer"), ("minimum", toJson (1 : Nat)),
       ("maximum", toJson (1000000 : Nat))])]
    ["sku", "units"]]

/-- Application-owned rights have exact, independent meanings. `lookup` and `reserve`
name a globally unique SKU; `low_stock` names a whole warehouse query, including counts and
pagination. `warehouse_totals` exposes all warehouses. Aggregate rights do not imply lookup
rights (or vice versa); a SKU's spelling never grants warehouse authority. Reserving also
requires lookup authority because its receipt discloses before/remaining stock. -/
def requiredCapabilities : Operation → List Capability.Access
  | .lookup sku => [.resource "inventory" "lookup" (.exact sku)]
  | .lowStock warehouse _ _ => [.resource "inventory" "low_stock" (.exact warehouse)]
  | .warehouseTotals => [.resource "inventory" "warehouse_totals" .all]
  | .reserve sku _ => [.resource "inventory" "lookup" (.exact sku),
      .resource "inventory" "reserve" (.exact sku)]

/-- The shared core applies capability demands and the frozen allow/ask/deny ceiling.
Reservation authority affects only this session's local stock, never an external service. -/
def policy (_ : Config) (_ : Operation) : Decision := .allow

def render (op : Operation) (result : Result op) : ToolResult :=
  {text := (encodeResult op result).compress}

def run (config : Config) (op : Operation) : Except String (Result op) := do
  query (← validateData config.applicationData) op

def application : Application where
  id := "inventory"
  version := 2
  Operation := Operation
  operationRepr := inferInstance
  operationDecEq := inferInstance
  operationToJson := inferInstance
  operationFromJson := inferInstance
  Result := Result
  resultToJson := fun op => ⟨encodeResult op⟩
  resultFromJson := fun op => ⟨decodeResult op⟩
  Witness := Witness
  witnessRepr := inferInstance
  witnessToJson := inferInstance
  witnessFromJson := inferInstance
  Resolution := Resolution
  resolutionToJson := inferInstance
  resolutionFromJson := inferInstance
  defaultInstructions := "You manage session-local inventory derived from a frozen seed and durable reservation receipts. Use inventory tools to establish facts. Distinguish missing items from zero stock; respect truncated pages. Reserve only quantities requested by the user and report the returned receipt. A new reserve call makes a new debit; do not repeat one to check its outcome. No external warehouse is changed and no commands can run."
  schemas := toolSchemas
  decode := decode
  name := name
  args := args
  requiredCapabilities := requiredCapabilities
  policy := policy
  render := render
  readOnly := fun op => match op with | .reserve _ _ => false | _ => true
  validateWitness := validateWitness
  resolve := resolve
  operatorResolution := fun _ => false

end Harness.Inventory
