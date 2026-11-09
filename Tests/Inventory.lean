import Harness.Applications.Inventory
import Harness.Applications.InventoryIO
import Harness.Core.Policy
import Harness.Adapter.Provider
import Plausible.Gen

namespace Tests.Inventory
open Lean Harness
open Harness.Inventory

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError s!"inventory test failed: {label}"

private def item (sku warehouse : String) (onHand reorderPoint : Nat) : Item :=
  {sku, name := s!"Product {sku}", warehouse, onHand, reorderPoint}

private def data : Dataset := {version := 1, items := #[
  item "A" "north" 12 20, item "B" "north" 3 10,
  item "C" "south" 0 30, item "D" "south" 8 10, item "E" "south" 15 12]}

private def raw (name : String) (fields : List (String × Json)) : RawCall :=
  {id := "query-1", name, input := Json.mkObj fields}

private def generate (seed : Nat) : IO (Dataset × Nat) := do
  let sample : Plausible.Gen (Dataset × Nat) := do
    let count ← Plausible.Gen.choose Nat 0 80 (by decide)
    let limit ← Plausible.Gen.choose Nat 1 17 (by decide)
    let mut items := #[]
    for i in [:count.val] do
      let warehouse ← Plausible.Gen.choose Nat 0 2 (by decide)
      let stock ← Plausible.Gen.choose Nat 0 1000000 (by decide)
      let point ← Plausible.Gen.choose Nat 0 1000000 (by decide)
      items := items.push {
        sku := s!"SKU-{i}", name := s!"Box \"λ🙂\" \\ {i}"
        warehouse := s!"WH-{warehouse.val}", onHand := stock.val, reorderPoint := point.val}
    return ({version := 1, items}, limit.val)
  match (Plausible.runRandWith seed sample).run ⟨80⟩ with
  | .ok value => pure value
  | .error error => throw <| Plausible.Gen.genFailure error

/-- Fixed-seed generated tests exercise serialization and pagination conservation,
not a second copy of the query implementation. No shrinking claim is made here. -/
private def generated : IO Unit := do
  for seed in [4000:4100] do
    let (input, limit) ← generate seed
    let json ← IO.ofExcept (JsonBounds.parse (toJson input).compress)
    let data ← IO.ofExcept (validateData json)
    check s!"seed {seed}: dataset wire roundtrip" (data == input)
    let totals ← IO.ofExcept (query data .warehouseTotals)
    let decodedTotals ← IO.ofExcept <| decodeResult .warehouseTotals
      (← IO.ofExcept (JsonBounds.parse (encodeResult .warehouseTotals totals).compress))
    check s!"seed {seed}: totals wire roundtrip" (decodedTotals == totals)
    for source in data.items do
      let found ← IO.ofExcept (query data (.lookup source.sku))
      let decoded ← IO.ofExcept <| decodeResult (.lookup source.sku)
        (← IO.ofExcept (JsonBounds.parse (encodeResult (.lookup source.sku) found).compress))
      check s!"seed {seed}: dependent lookup roundtrip" (decoded == some source)
      check s!"seed {seed}: lookup wrong SKU refuses" <|
        (decodeResult (.lookup "missing") (encodeResult (.lookup source.sku) found)).toOption.isNone
    for warehouse in totals do
      let expected := (data.items.filter (fun row => row.warehouse == warehouse.warehouse &&
        row.onHand < row.reorderPoint)).map (·.sku)
      let mut offset := 0
      let mut collected : Array String := #[]
      let mut complete := false
      for _ in [:81] do
        if !complete then
          let op := Operation.lowStock warehouse.warehouse offset limit
          let page ← IO.ofExcept (query data op)
          let decoded ← IO.ofExcept <| decodeResult op
            (← IO.ofExcept (JsonBounds.parse (encodeResult op page).compress))
          check s!"seed {seed}: dependent page roundtrip" (decoded == page)
          collected := collected ++ page.rows.map (·.item.sku)
          match page.nextOffset with
          | some next =>
            check s!"seed {seed}: page makes progress" (offset < next)
            offset := next
          | none => complete := true
      check s!"seed {seed}: all matching rows retrieved exactly once" (complete && collected == expected)

/-- Typed inventory, strict boundary and data-dependent query fixtures; no network or shell. -/
def run : IO Unit := do
  let validated ← IO.ofExcept (validateData (toJson data))
  check "dataset roundtrip" (validated == data)
  let totals ← IO.ofExcept (query validated .warehouseTotals)
  check "totals computed from actual quantities" <|
    totals == #[{warehouse := "north", itemCount := 2, lowStockCount := 2, shortfallUnits := 15},
      {warehouse := "south", itemCount := 3, lowStockCount := 2, shortfallUnits := 32}]
  let changed := {data with items := data.items.set! 2 (item "C" "south" 29 30)}
  let changed ← IO.ofExcept (validateData (toJson changed))
  let changedTotals ← IO.ofExcept (query changed .warehouseTotals)
  check "changed input changes computed answer" <|
    changedTotals[1]?.any (fun row => row.shortfallUnits == 3) && totals != changedTotals
  let found ← IO.ofExcept (query data (.lookup "C"))
  let absent ← IO.ofExcept (query data (.lookup "absent"))
  check "lookup distinguishes absent from zero stock" <|
    found.any (fun row => row.onHand == 0) && absent.isNone
  let first ← IO.ofExcept (query data (.lowStock "south" 0 1))
  let second ← IO.ofExcept (query data (.lowStock "south" 1 1))
  check "pagination retrieves every omitted row once" <|
    first.rows.map (·.item.sku) == #["C"] && first.matched == 2 && first.nextOffset == some 1 &&
    first.truncated && second.rows.map (·.item.sku) == #["D"] && second.nextOffset.isNone &&
    !second.truncated && second.offset == 1
  let beyond ← IO.ofExcept (query data (.lowStock "south" 512 1))
  check "page beyond end is explicitly empty" <|
    beyond.rows.isEmpty && beyond.matched == 2 && beyond.nextOffset.isNone
  check "unknown warehouse is an error" (query data (.lowStock "missing" 0 1)).toOption.isNone
  check "unknown coding tool rejected" (decode (raw "process" [("argv", toJson #["sh"])] )).toOption.isNone
  check "arbitrary path argument rejected" (decode (raw "lookup" [
    ("sku", toJson "C"), ("path", toJson "/etc/passwd")])).toOption.isNone
  check "path-shaped SKU rejected" (decode (raw "lookup" [("sku", toJson "../secret")])).toOption.isNone
  check "optional arguments default exactly" <|
    (decode (raw "low_stock" [("warehouse", toJson "south")])).toOption == some (.lowStock "south" 0 50)
  for value in #[toJson (0 : Nat), toJson (101 : Nat), toJson true, toJson "1"] do
    check "invalid page limit rejected" (decode (raw "low_stock" [
      ("warehouse", toJson "south"), ("limit", value)])).toOption.isNone
  check "offset limit enforced" (decode (raw "low_stock" [
    ("warehouse", toJson "south"), ("offset", toJson (513 : Nat))])).toOption.isNone
  check "dataset duplicate SKU rejected" <|
    (validateData (toJson {data with items := data.items.push (item "A" "west" 1 2)})).toOption.isNone
  check "dataset unknown field rejected" <|
    (validateData ((toJson data).mergeObj (Json.mkObj [("path", toJson "/tmp/other")]))).toOption.isNone
  check "unsupported dataset version rejected" (validateData (toJson {data with version := 2})).toOption.isNone
  check "quantity cap enforced" <|
    (validateData (toJson {data with items := #[item "A" "north" 1000001 2]})).toOption.isNone
  let firstJson := encodeResult (.lowStock "south" 0 1) first
  let foundJson := encodeResult (.lookup "C") found
  let totalsJson := encodeResult .warehouseTotals totals
  check "lookup codec roundtrip" <|
    (decodeResult (.lookup "C") foundJson).toOption == some found
  check "page codec roundtrip" <|
    (decodeResult (.lowStock "south" 0 1) firstJson).toOption == some first
  check "summary codec roundtrip" <|
    (decodeResult .warehouseTotals totalsJson).toOption == some totals
  check "cross-result types are rejected" <|
    (decodeResult (.lookup "C") totalsJson).toOption.isNone &&
    (decodeResult .warehouseTotals firstJson).toOption.isNone &&
    (decodeResult (.lowStock "south" 0 1) foundJson).toOption.isNone
  check "lookup wrong SKU rejected" (decodeResult (.lookup "D") foundJson).toOption.isNone
  check "wrong warehouse result rejected" (decodeResult (.lowStock "north" 0 1) firstJson).toOption.isNone
  check "wrong page result rejected" (decodeResult (.lowStock "south" 1 1) firstJson).toOption.isNone
  let forged := encodeResult (.lowStock "south" 0 1) {first with nextOffset := some 0}
  check "nonprogressing continuation rejected" (decodeResult (.lowStock "south" 0 1) forged).toOption.isNone
  let cfg : Config := {model := "scripted", applicationData := toJson data}
  let session := s!"/tmp/lean-harness-inventory-io-{← Native.getPid}-{← IO.monoNanosNow}"
  Native.mkdir session 448
  try
    InventoryIO.runtime.initializeSession session cfg
    let context : ToolContext := {
      sessionPath := session, sessionId := session, operationId := 1
      workspace := "", timeoutMs := 1000, outputBytes := 32
      artifactDir := "", cancelPath := ""}
    let oversized ← InventoryIO.runtime.execute cfg context ⟨"query-small", .warehouseTotals⟩
    check "oversized result becomes failure, never a partial typed value" <|
      match oversized with | .failure _ => true | _ => false
    let bounded ← InventoryIO.runtime.execute cfg {context with outputBytes := totalsJson.compress.utf8ByteSize}
      ⟨"query-bounded", .warehouseTotals⟩
    check "result exactly at byte ceiling remains its original dependent type" <|
      match bounded with
      | .success value => (application.render .warehouseTotals value).text == totalsJson.compress
      | _ => false
    let noTime ← InventoryIO.runtime.execute cfg {context with timeoutMs := 0}
      ⟨"query-no-time", .warehouseTotals⟩
    check "zero local deadline is failure without a typed timeout" <|
      match noTime with | .failure _ => true | _ => false
    let expired ← InventoryIO.runtime.execute cfg {context with invocationDeadlineMs := some 0}
      ⟨"query-expired", .warehouseTotals⟩
    check "expired invocation is interrupted" <|
      match expired with | .interrupted _ none => true | _ => false
    let cancelPath := session ++ "/cancel"
    IO.FS.writeFile cancelPath "cancel\n"
    let cancelled ← InventoryIO.runtime.execute cfg {
      context with cancelPath, timeoutMs := 0, invocationDeadlineMs := some 0}
      ⟨"query-cancelled", .warehouseTotals⟩
    check "durable cancellation wins over invocation and local deadlines" <|
      match cancelled with | .interrupted message none => message.contains "cancelled" | _ => false
  finally
    IO.FS.removeDirAll session
  for invalid in #[{cfg with workspace := "/tmp"}, {cfg with commands := .allow},
      {cfg with toolchainRoots := #["/usr"]}, {cfg with executionProfile := .bubblewrap}] do
    let refused ← try
      let _ ← InventoryIO.prepareConfig invalid
      pure false
    catch _ => pure true
    check "coding-only authority is rejected at inventory preparation" refused
  let permission := fun config op => Harness.policy config
    ({id := "permission-test", operation := op} : Call application)
  check "permission modes apply to exact queries" <|
    permission cfg .warehouseTotals == .allow &&
    permission {cfg with toolPolicy := .deny} (.lookup "C") == .deny &&
    permission {cfg with toolPolicy := .ask} (.lowStock "south" 0 1) == .ask
  check "readonly recovery has no mutation resolution" <|
    application.readOnly .warehouseTotals && !application.mayAbandon .warehouseTotals &&
    !application.settledTimeout cfg .warehouseTotals &&
    (application.validateWitness .warehouseTotals
      ⟨"/tmp/inventory-test", 1, "C", 1⟩).toOption.isNone &&
    (application.resolve .warehouseTotals none
      ⟨"/tmp/inventory-test", 1, "C", 1, 2, 1⟩).toOption.isNone
  let request : ModelRequest := {
    model := "scripted", system := application.defaultInstructions
    messages := [], maxTokens := 64, tools := application.schemas}
  check "provider offers only inventory schemas" <|
    ((Provider.encodeRequest request).getObjVal? "tools").toOption == some (toJson toolSchemas) &&
    toolSchemas.size == 4 && !toolSchemas.any (fun schema =>
      (schema.getObjValAs? String "name").toOption == some "process")
  check "summaries never offer application tools" <|
    ((Provider.encodeRequest {request with purpose := .summary}).getObjVal? "tools").toOption.isNone
  generated

end Tests.Inventory
