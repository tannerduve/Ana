import Harness.Applications.Inventory

/-! Pure reservation contracts. Expected stock and receipt values are written
independently of the helper; recovery and codec negatives include valid-looking
receipts whose identity or pre-debit stock belongs to a different operation. -/
namespace Tests.InventoryReservations
open Lean Harness Harness.Inventory

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError s!"inventory reservation: {label}"

private def alpha : Item :=
  {sku := "A", name := "Alpha", warehouse := "north", onHand := 10, reorderPoint := 12}
private def beta : Item :=
  {sku := "B", name := "Beta", warehouse := "south", onHand := 4, reorderPoint := 4}
private def seed : Dataset := {version := 1, items := #[alpha, beta]}

private def key : ReservationKey := ⟨"/tmp/inventory-session", 7⟩
private def witness : Witness := ⟨key.sessionId, key.operationId, "A", 3⟩
private def expected : Reservation := ⟨key.sessionId, key.operationId, "A", 3, 10, 7⟩

def run : IO Unit := do
  let (next, receipt) ← IO.ofExcept (reserve seed key (.reserve "A" 3))
  check "debit and receipt exact" <|
    receipt == expected && next.version == 1 && next.items.size == 2 &&
    next.items == #[{alpha with onHand := 7}, beta]
  check "input value remains unchanged" (seed.items == #[alpha, beta])
  check "query observes current stock" <|
    (query next (.lookup "A")).toOption == some (some {alpha with onHand := 7})
  let page ← IO.ofExcept (query next (.lowStock "north" 0 10))
  check "replenishment reflects reservation" (page.rows.map (·.units) == #[5])
  for op in [.reserve "A" 0, .reserve "A" 11, .reserve "missing" 1,
      .reserve "A" 1000001, .lookup "A"] do
    check "invalid debit returns no update" (reserve seed key op).toOption.isNone
  check "unvalidated duplicate dataset refused" <|
    (reserve {seed with items := seed.items.push alpha} key (.reserve "A" 1)).toOption.isNone
  for invalid in [⟨"", 7⟩, ⟨"bad\nidentity", 7⟩, ⟨key.sessionId, 18446744073709551616⟩] do
    check "invalid runner key refused" (reserve seed invalid (.reserve "A" 1)).toOption.isNone
  check "query cannot bypass durable mutation path" (query seed (.reserve "A" 3)).toOption.isNone
  check "ledger replay recomputes exact update" ((applyReservation seed receipt).toOption == some next)
  check "same receipt cannot debit twice" (applyReservation next receipt).toOption.isNone
  let (empty, all) ← IO.ofExcept (reserve next {key with operationId := 8} (.reserve "A" 7))
  check "exact remaining stock may be reserved" (empty.items == #[{alpha with onHand := 0}, beta] && all.before == 7 && all.remaining == 0)
  check "stock cannot go below zero" (reserve empty {key with operationId := 9} (.reserve "A" 1)).toOption.isNone
  check "plausible receipt from different stock rejected" <|
    (validateReservation {receipt with before := 11, remaining := 8}).toOption.isSome &&
    (applyReservation seed {receipt with before := 11, remaining := 8}).toOption.isNone
  let raw : RawCall := {id := "model-call", name := "reserve", input := Json.mkObj [
    ("sku", toJson "A"), ("units", toJson (3 : Nat))]}
  check "typed model arguments accepted" ((decode raw).toOption == some (.reserve "A" 3))
  for field in ["sessionId", "operationId", "before", "remaining"] do
    check "model cannot supply trusted receipt fields" <|
      (decode {raw with input := raw.input.mergeObj (Json.mkObj [(field, toJson (7 : Nat))])}).toOption.isNone
  for invalid in #[toJson (0 : Nat), toJson (-1 : Int), toJson true, toJson "3"] do
    check "nonpositive or wrong-typed quantity refused" <|
      (decode {raw with input := Json.mkObj [("sku", toJson "A"), ("units", invalid)]}).toOption.isNone
  let json := encodeResult (.reserve "A" 3) receipt
  check "receipt codec roundtrip" ((decodeResult (.reserve "A" 3) json).toOption == some receipt)
  check "result codec binds exact operation arguments" <|
    (decodeResult (.reserve "B" 3) json).toOption.isNone &&
    (decodeResult (.reserve "A" 2) json).toOption.isNone
  check "strict receipt fields" <|
    (reservationFromJson ((toJson receipt).mergeObj (Json.mkObj [("extra", toJson true)]))).toOption.isNone
  check "strict witness roundtrip" ((witnessFromJson (toJson witness)).toOption == some witness)
  check "strict witness fields" <|
    (witnessFromJson ((toJson witness).mergeObj (Json.mkObj [("remaining", toJson (7 : Nat))]))).toOption.isNone
  check "matching receipt settles" <|
    match resolve (.reserve "A" 3) (some witness) receipt with
    | .ok (.success found) => found == expected
    | _ => false
  check "missing witness cannot settle" (resolve (.reserve "A" 3) none receipt).toOption.isNone
  for forged in [{receipt with sessionId := "/tmp/another-session"}, {receipt with operationId := 8},
      {receipt with sku := "B"}, {receipt with units := 2, remaining := 8},
      {receipt with remaining := 8}, {receipt with before := 2, remaining := 0}] do
    check "mismatched or impossible receipt refused" <|
      (resolve (.reserve "A" 3) (some witness) forged).toOption.isNone
  check "witness cannot name another operation" <|
    (validateWitness (.reserve "A" 3) {witness with sku := "B"}).toOption.isNone &&
    (validateWitness (.lookup "A") witness).toOption.isNone
  check "mutation cannot use lost-read or abandonment recovery" <|
    !application.readOnly (.reserve "A" 3) && !application.mayAbandon (.reserve "A" 3) &&
    application.readOnly (.lookup "A") && application.version == 2
  IO.println "inventory reservations: stock arithmetic, identity, strict codecs and witnessed recovery passed"

end Tests.InventoryReservations
