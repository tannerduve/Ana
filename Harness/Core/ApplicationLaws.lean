import Harness.Core.Application

/-!
Laws for a statically installed application. Validity is an independently stated domain predicate,
not success of a codec round trip. Runtime implementations additionally owe the effect/evidence
contract documented in `docs/ApplicationContracts.md`; these pure laws do not establish IO truth.
-/
namespace Harness
open Lean

structure ApplicationLaws (app : Application) where
  ValidOperation : app.Operation → Prop
  ValidResult : (op : app.Operation) → app.Result op → Prop
  /-- The model argument decoder admits only independently valid operations. -/
  decode_valid : ∀ raw op, app.decode raw = .ok op → ValidOperation op
  /-- Storage codecs, as used by the journal, preserve valid operations. -/
  operation_roundtrip : ∀ op, ValidOperation op →
    app.operationFromJson.fromJson? (app.operationToJson.toJson op) = .ok op
  /-- Dependent result codecs preserve valid values for the exact operation. -/
  result_roundtrip : ∀ op result, ValidOperation op → ValidResult op result →
    (app.resultFromJson op).fromJson? ((app.resultToJson op).toJson result) = .ok result
  /-- Optional partial results must not collapse `some value` into JSON null. -/
  result_not_null : ∀ op result, ValidResult op result →
    (app.resultToJson op).toJson result ≠ .null
  /-- App-specific model representation, stated independently of `app.render`. -/
  Rendered : (op : app.Operation) → app.Result op → ToolResult → Prop
  render_faithful : ∀ op result, ValidOperation op → ValidResult op result →
    Rendered op result (app.render op result)

/-- Success and retained partial values must satisfy the same dependent contract.
An error carries no alleged result; it does not imply rollback or effect settlement. -/
def ApplicationLaws.ValidObservation (laws : ApplicationLaws app) (op : app.Operation) :
    ToolObservation (app.Result op) → Prop
  | .success value => laws.ValidResult op value
  | .failure _ => True
  | .timedOut output | .interrupted _ output | .uncertain _ output =>
    ∀ value ∈ output, laws.ValidResult op value

end Harness
