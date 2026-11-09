import Harness.Core.Transition
import Harness.Applications.Inventory
import Harness.Proofs.ApplicationCapabilities

/-! Call-level regressions for the installed applications. No filesystem/process effects run.
Inventory query assertions demonstrate why warehouse aggregates and SKU lookups are independent
rights, and why a reservation needs disclosure as well as mutation authority. -/
namespace Tests.ApplicationCapabilities
open Harness Lean Capability

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError s!"application capabilities: {label}"

private def codingCall (operation : ToolOp) : ToolCall := ⟨"coding-call", operation⟩
private def inventoryCall (operation : Inventory.Operation) : Call Inventory.application :=
  ⟨"inventory-call", operation⟩

private def proposed (config : Config) (call : Call app) : State app :=
  let raw : RawCall := ⟨call.id, app.name call.operation, app.args call.operation⟩
  let block := Json.mkObj [("type", toJson "tool_use"), ("id", toJson raw.id),
    ("name", toJson raw.name), ("input", raw.input)]
  consumeModel (admitTask (init "capability-test" config "task" app))
    (.success {content := #[block], calls := [raw], text := "", stop := .toolUse})

private def allowed (label : String) (config : Config) (call : Call app) : IO Unit := do
  check (label ++ ": permission") (authorized config none call)
  let requested := proposed config call
  check (label ++ ": batch admitted") (requested.seenCallIds == [call.id])
  let state := admitTool requested call []
  check (label ++ ": dispatch reservation") <|
    state.toolDispatches == 1 && match state.phase with
    | .tool actual [] => actual == call
    | _ => false

private def denied (label : String) (config : Config) (call : Call app) : IO Unit := do
  check (label ++ ": approval cannot override missing authority")
    (!authorized config (some call) call && policy config call == .deny)
  let requested := proposed config call
  check (label ++ ": batch admitted before capability check") (requested.seenCallIds == [call.id])
  let state := admitTool requested call []
  check (label ++ ": no dispatch or approval loop") <|
    state.toolDispatches == 0 && state.grant.isNone && match state.phase with
    | .controlTools [] => true
    | _ => false
  let message ← match state.history.getLast? with
    | some message => pure message
    | none => throw <| IO.userError "denial omitted its model-visible result"
  check (label ++ ": explicit denied result")
    ((message.content[0]!.getObjValAs? Bool "is_error").toOption == some true)

private def northA : Inventory.Item :=
  {sku := "A", name := "North item", warehouse := "north", onHand := 8, reorderPoint := 10}
private def northB : Inventory.Item :=
  {sku := "OTHER-NORTH", name := "Other north item", warehouse := "north", onHand := 1, reorderPoint := 4}
private def south : Inventory.Item :=
  {sku := "N-SOUTH", name := "South item", warehouse := "south", onHand := 2, reorderPoint := 5}
private def seed : Inventory.Dataset := {version := 1, items := #[northA, south, northB]}

def run : IO Unit := do
  let base : Config := {model := "scripted", commands := .allow}
  let sourceOnly := {base with capabilityPolicy := [[.read (.tree "src"), .write (.tree "src")]]}
  let edit : EditArgs := {
    path := "src/main.py", old := "old", new := "new",
    expectedSha256 := String.ofList (List.replicate 64 'a')}
  allowed "subtree listing" sourceOnly (codingCall (.listFiles {path := "src", limit := 1}))
  allowed "subtree search" sourceOnly (codingCall (.searchFiles {path := "src", query := "needle", limit := 1}))
  allowed "exact read under subtree" sourceOnly (codingCall (.readFile {path := "src/main.py"}))
  allowed "edit has both authorities" sourceOnly (codingCall (.editFile edit))
  allowed "create under writable subtree" sourceOnly (codingCall (.createFile {path := "src/new.py", content := "new"}))
  denied "listing parent exposes other names" sourceOnly (codingCall (.listFiles {path := "."}))
  denied "search parent exposes other content" sourceOnly (codingCall (.searchFiles {path := ".", query := "needle"}))
  denied "path prefix is not a component" sourceOnly (codingCall (.readFile {path := "src-private/secret"}))
  let exactRead := {base with capabilityPolicy := [[.read (.exact "src/main.py")]]}
  allowed "exact read grant" exactRead (codingCall (.readFile {path := "src/main.py"}))
  denied "exact grant cannot authorize recursive search" exactRead
    (codingCall (.searchFiles {path := "src/main.py", query := "needle"}))
  denied "read authority cannot edit" exactRead (codingCall (.editFile edit))
  let writeOnly := {base with capabilityPolicy := [[.write (.exact "src/main.py")]]}
  denied "write authority cannot inspect edit preimage" writeOnly (codingCall (.editFile edit))
  allowed "create requires write rather than edit preimage authority" writeOnly
    (codingCall (.createFile {path := "src/main.py", content := "replacement", overwrite := true}))
  let command : ProcessArgs := {argv := #["/usr/bin/true"], cwd := "src"}
  denied "read/write does not grant opaque process authority" sourceOnly (codingCall (.runProcess command))
  let oneCommand := {base with capabilityPolicy := [[.process command.argv command.cwd]]}
  allowed "exact command invocation" oneCommand (codingCall (.runProcess command))
  denied "changed command argument" oneCommand
    (codingCall (.runProcess {command with argv := #["/usr/bin/true", "extra"]}))
  denied "changed command directory" oneCommand
    (codingCall (.runProcess {command with cwd := "tests"}))
  denied "capability cannot widen command deny"
    {oneCommand with commands := .deny} (codingCall (.runProcess command))
  let artifact := codingCall (.readArtifact {id := "retained-one"})
  let oneArtifact := {base with capabilityPolicy := [[.artifact "retained-one"]]}
  check "artifact byte capability has an independent identity"
    (policy oneArtifact artifact == .allow &&
      policy oneArtifact (codingCall (.readArtifact {id := "retained-two"})) == .deny)
  let missingArtifact := admitTool (init "artifact-test" oneArtifact "task") artifact []
  check "capability does not invent registered artifact authority"
    (missingArtifact.toolDispatches == 0 && match missingArtifact.phase with
      | .controlTools [] => true | _ => false)

  let cfg : Config := {model := "scripted", applicationData := toJson seed}
  let queries := {cfg with capabilityPolicy := [[
    .resource "inventory" "lookup" (.exact "A"),
    .resource "inventory" "low_stock" (.exact "north")]]}
  allowed "exact SKU lookup" queries (inventoryCall (.lookup "A"))
  denied "warehouse query grant does not imply SKU lookup" queries
    (inventoryCall (.lookup "OTHER-NORTH"))
  denied "SKU prefix grants no authority" queries (inventoryCall (.lookup "N-SOUTH"))
  allowed "explicit warehouse aggregate" queries (inventoryCall (.lowStock "north" 0 1))
  denied "other warehouse aggregate" queries (inventoryCall (.lowStock "south" 0 1))
  denied "global totals require independent global right" queries (inventoryCall .warehouseTotals)
  let page ← IO.ofExcept (Inventory.query seed (.lowStock "north" 0 1))
  check "warehouse permission covers count and later page, not only returned SKU" <|
    page.matched == 2 && page.rows.map (·.item.sku) == #["A"] && page.nextOffset == some 1
  let nextPage ← IO.ofExcept (Inventory.query seed (.lowStock "north" 1 1))
  check "warehouse scope follows data association, not SKU prefix" <|
    nextPage.rows.map (·.item.sku) == #["OTHER-NORTH"] && nextPage.nextOffset.isNone
  let totalsOnly := {cfg with capabilityPolicy := [[.resource "inventory" "warehouse_totals" .all]]}
  allowed "explicit global totals" totalsOnly (inventoryCall .warehouseTotals)
  denied "aggregate right does not imply raw item lookup" totalsOnly (inventoryCall (.lookup "A"))
  denied "named resource is not all warehouses"
    {cfg with capabilityPolicy := [[.resource "inventory" "warehouse_totals" (.exact "north")]]}
    (inventoryCall .warehouseTotals)
  let reserveA := inventoryCall (.reserve "A" 2)
  denied "read-only query policy cannot reserve" queries reserveA
  denied "reservation right alone cannot disclose receipt stock"
    {cfg with capabilityPolicy := [[.resource "inventory" "reserve" (.exact "A")]]} reserveA
  let reserveBoth := {cfg with capabilityPolicy := [[
    .resource "inventory" "lookup" (.exact "A"), .resource "inventory" "reserve" (.exact "A")]]}
  allowed "reservation has disclosure and mutation authority" reserveBoth reserveA
  denied "reservation rights remain exact SKU" reserveBoth (inventoryCall (.reserve "OTHER-NORTH" 2))
  denied "resource application identity cannot be substituted"
    {cfg with capabilityPolicy := [[.resource "another-application" "lookup" (.exact "A")]]}
    (inventoryCall (.lookup "A"))
  let (stock, receipt) ← IO.ofExcept (Inventory.reserve seed ⟨"session", 1⟩ (.reserve "A" 2))
  check "receipt contains protected stock observation" (receipt.before == 8 && receipt.remaining == 6)
  check "reservation affects only the exact SKU"
    (stock.items == #[{northA with onHand := 6}, south, northB])
  check "lookup reflects reserved stock"
    ((Inventory.query stock (.lookup "A")).toOption == some (some {northA with onHand := 6}))
  denied "global deny remains authoritative" {reserveBoth with toolPolicy := .deny} reserveA
  denied "empty capability layer denies query" {cfg with capabilityPolicy := [[]]}
    (inventoryCall (.lookup "A"))
  allowed "absent capability restriction preserves legacy query" cfg (inventoryCall (.lookup "A"))
  IO.println "application capabilities: exact call scope, edit preimage, aggregate disclosure and reservation dual authority passed"

end Tests.ApplicationCapabilities
