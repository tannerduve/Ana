import Harness.Applications.Inventory
import Harness.Proofs.ApplicationCodec

namespace Harness.Inventory
open Lean ApplicationCodec ExceptRules

theorem operation_roundtrip (op : Operation) :
    (fromJson? (toJson op) : Except String Operation) = .ok op := by
  cases op <;>
    simp only [fromJson?, toJson, instFromJsonOperation.fromJson, instToJsonOperation.toJson, tag_singleton]
  all_goals simp [Json.parseCtorFields, Array.mapM_eq_mapM_toList]
  all_goals rfl

theorem item_validate (item : Item) (valid : validItem item = true) :
    validateItem item = .ok () := by
  simp_all [validItem, validateItem]

theorem item_roundtrip (item : Item) (valid : validItem item = true) :
    itemFromJson (toJson item) = .ok item := by
  have shape : exactFields (toJson item) ["sku", "name", "warehouse", "onHand", "reorderPoint"] = .ok () := by
    rfl
  have parsed : (fromJson? (toJson item) : Except String Item) = .ok item := by cases item; rfl
  simp only [itemFromJson, shape, ok_bind, parsed, item_validate item valid, pure_ok]

theorem receipt_validate (receipt : Reservation) (valid : validReceipt receipt = true) :
    validateReservation receipt = .ok () := by
  simp_all [validReceipt, validateReservation]

theorem receipt_roundtrip (receipt : Reservation) (valid : validReceipt receipt = true) :
    reservationFromJson (toJson receipt) = .ok receipt := by
  change (do
    exactFields (toJson receipt) ["sessionId", "operationId", "sku", "units", "before", "remaining"]
    validateReservation receipt
    pure receipt) = _
  have shape : exactFields (toJson receipt) ["sessionId", "operationId", "sku", "units", "before", "remaining"] = .ok () := by rfl
  rw [shape]
  simp only [ok_bind, receipt_validate receipt valid, pure_ok]

theorem row_roundtrip (row : ReorderRow) (valid : validItem row.item = true) :
    rowFromJson (toJson row) = .ok row := by
  change (do
    let item ← itemFromJson (toJson row.item)
    pure (ReorderRow.mk item row.units)) = _
  rw [item_roundtrip row.item valid]
  rfl

theorem page_roundtrip (page : StockPage) (bounded : page.rows.size ≤ 100)
    (valid : ∀ row ∈ page.rows, validItem row.item = true) :
    pageFromJson (toJson page) = .ok page := by
  have rows : (page.rows.map toJson).mapM rowFromJson = .ok page.rows :=
    mapM_encode toJson rowFromJson page.rows (fun row member => row_roundtrip row (valid row member))
  change (do
    unless (page.rows.map toJson).size ≤ 100 do throw "too many low-stock rows"
    let rows ← (page.rows.map toJson).mapM rowFromJson
    let nextOffset ← (fromJson? (toJson page.nextOffset) : Except String (Option Nat))
    pure (StockPage.mk rows page.matched page.offset nextOffset page.truncated)) = _
  simp only [Array.size_map, bounded, ↓reduceIte, pure_ok]
  rw [rows, option_nat_roundtrip]
  rfl

theorem summary_roundtrip (summary : WarehouseSummary) :
    summaryFromJson (toJson summary) = .ok summary := by cases summary; rfl

theorem result_roundtrip (op : Operation) (result : Result op)
    (valid : validResult op result = true) : decodeResult op (encodeResult op result) = .ok result := by
  cases op with
  | lookup sku =>
    cases result with
    | none => rfl
    | some item =>
      have validItem : Inventory.validItem item = true := by
        simp only [validResult, Bool.and_eq_true] at valid
        exact valid.1
      change (do
        let value ← Option.some <$> itemFromJson (toJson item)
        unless validResult (.lookup sku) value do throw "lookup result has invalid fields or a different SKU"
        pure value) = _
      rw [item_roundtrip item validItem]
      simp [valid]
  | lowStock warehouse offset limit =>
    have items : ∀ row ∈ result.rows, validItem row.item = true := by
      simp only [validResult, validPage, Bool.and_eq_true] at valid
      intro row member
      have h := Array.all_eq_true_iff_forall_mem.mp valid.1.2 row member
      simp only [Bool.and_eq_true] at h
      exact h.1.1.1
    have bounded : result.rows.size ≤ 100 := by
      have h := valid
      simp only [validResult, validPage, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      have upper := Nat.min_le_left limit (result.matched - result.offset)
      omega
    change (do
      let page ← pageFromJson (toJson result)
      unless validResult (.lowStock warehouse offset limit) page do
        throw "invalid low-stock result bounds, continuation, warehouse, shortfall, or duplicate SKU"
      pure page) = _
    rw [page_roundtrip result bounded items]
    simp [valid]
  | warehouseTotals =>
    have rows : (result.map toJson).mapM summaryFromJson = .ok result :=
      mapM_encode toJson summaryFromJson result (fun value _ => summary_roundtrip value)
    have bounded : result.size ≤ 64 := by
      have h := valid
      simp only [validResult, validSummaries, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1.1
    change (do
      unless (result.map toJson).size ≤ 64 do throw "too many warehouse summaries"
      let rows ← (result.map toJson).mapM summaryFromJson
      unless validResult .warehouseTotals rows do throw "invalid or duplicate warehouse summaries"
      pure rows) = _
    simp only [Array.size_map, bounded, ↓reduceIte, pure_ok]
    rw [rows]
    simp [valid]
  | reserve sku units =>
    have vr : validReceipt result = true := by
      simp only [validResult, Bool.and_eq_true] at valid
      exact valid.1.1
    change (do
      let receipt ← reservationFromJson (toJson result)
      unless validResult (.reserve sku units) receipt do
        throw "reservation result has invalid fields or belongs to different arguments"
      pure receipt) = _
    rw [receipt_roundtrip result vr]
    simp [valid]

set_option maxHeartbeats 1000000 in
theorem decode_valid (raw : RawCall) :
    ExceptSuccess (fun op => validOperation op = true) (decode raw) := by
  unfold decode
  split
  all_goals simp only [ExceptSuccess.bind_iff, ExceptSuccess.if_iff, ExceptSuccess.error_iff,
    ExceptSuccess.ok_iff, pure_ok, throw_error, error_bind]
  all_goals repeat' first
    | (solve | simp_all [validOperation])
    | (constructor)
    | (intro)
    | (split)
  all_goals simp_all [validOperation]
  all_goals rename_i checked
  all_goals simp only [bind, Except.bind] at checked
  all_goals repeat' first
    | (split at checked)
    | (solve | simp_all)
    | (cases checked)

theorem decoded_result_valid (op : Operation) (json : Json) :
    ExceptSuccess (fun result => validResult op result = true) (decodeResult op json) := by
  cases op <;> simp only [decodeResult]
  all_goals simp only [ExceptSuccess.bind_iff, ExceptSuccess.if_iff, ExceptSuccess.error_iff,
    ExceptSuccess.ok_iff, pure_ok, throw_error, error_bind]
  all_goals simp_all

/-- Inventory communicates the canonical tagged result and makes no process-exit,
file-identity or artifact claims. The later shared normalization is specified separately. -/
def Rendered (op : Operation) (result : Result op) (visible : ToolResult) : Prop :=
  visible.text = (encodeResult op result).compress ∧ visible.exitCode = none ∧
  visible.sha256 = none ∧ visible.artifacts = #[]

def laws : ApplicationLaws application where
  ValidOperation := fun op => validOperation op = true
  ValidResult := fun op result => validResult op result = true
  decode_valid := decode_valid
  operation_roundtrip := fun op _ => operation_roundtrip op
  result_roundtrip := fun op result _ valid => result_roundtrip op result valid
  result_not_null := by intro op result _; cases op <;> intro impossible <;> cases impossible
  Rendered := Rendered
  render_faithful := fun _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩

end Harness.Inventory
