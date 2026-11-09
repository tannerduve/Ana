import Harness.Applications.InventoryData

/-! Field-level contracts independent of JSON parsing/encoding. They establish admissible data,
not that an observation accurately describes an external warehouse or the current receipt ledger. -/
namespace Harness.Inventory

def validItem (item : Item) : Bool :=
  validIdentifier item.sku && validIdentifier item.warehouse &&
  !item.name.trimAscii.toString.isEmpty && item.name.utf8ByteSize ≤ 256 &&
  item.name.toList.all (fun c => c.toNat ≥ 32 && c.toNat != 127) &&
  item.onHand ≤ 1000000 && item.reorderPoint ≤ 1000000

def validOperation : Operation → Bool
  | .lookup sku => validIdentifier sku
  | .lowStock warehouse offset limit =>
    validIdentifier warehouse && offset ≤ 512 && 0 < limit && limit ≤ 100
  | .warehouseTotals => true
  | .reserve sku units => validReservationArgs sku units

def validReceipt (receipt : Reservation) : Bool :=
  validReservationKey ⟨receipt.sessionId, receipt.operationId⟩ &&
  validReservationArgs receipt.sku receipt.units && receipt.before ≤ 1000000 &&
  receipt.units ≤ receipt.before && receipt.remaining + receipt.units == receipt.before

def validPage (warehouse : String) (requestedOffset limit : Nat) (page : StockPage) : Bool :=
  let more := page.offset + page.rows.size < page.matched
  page.offset == requestedOffset && page.offset ≤ 512 && 0 < limit && limit ≤ 100 &&
  page.matched ≤ 512 && page.rows.size == min limit (page.matched - page.offset) &&
  page.truncated == more && page.nextOffset == (if more then some (page.offset + page.rows.size) else none) &&
  page.rows.all (fun row => validItem row.item && row.item.warehouse == warehouse &&
    row.units == shortfall row.item && row.units > 0) &&
  decide ((page.rows.toList.map (fun row => row.item.sku)).Nodup)

def validSummary (summary : WarehouseSummary) : Bool :=
  validIdentifier summary.warehouse && 0 < summary.itemCount && summary.itemCount ≤ 512 &&
  summary.lowStockCount ≤ summary.itemCount && summary.shortfallUnits ≤ summary.lowStockCount * 1000000

def validSummaries (rows : Array WarehouseSummary) : Bool :=
  rows.size ≤ 64 && rows.all validSummary &&
  decide ((rows.toList.map (·.warehouse)).Nodup) &&
  (rows.toList.map (·.itemCount)).sum ≤ 512

def validResult : (op : Operation) → Result op → Bool
  | .lookup _, none => true
  | .lookup sku, some item => validItem item && item.sku == sku
  | .lowStock warehouse offset limit, page => validPage warehouse offset limit page
  | .warehouseTotals, rows => validSummaries rows
  | .reserve sku units, receipt => validReceipt receipt && receipt.sku == sku && receipt.units == units

end Harness.Inventory
