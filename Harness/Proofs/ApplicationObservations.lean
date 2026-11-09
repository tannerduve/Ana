import Harness.Proofs.ApplicationCodec
import Harness.Core.Effects

/-! Exact codecs for the observations carried by the shared dependent tool effect.
An optional partial value is preserved only when its valid encoding is non-null. -/
namespace Harness
open Lean ApplicationCodec ExceptRules
variable {app : Application}

theorem application_observation_roundtrip (laws : ApplicationLaws app) (op : app.Operation)
    (validOp : laws.ValidOperation op) (observation : ToolObservation (app.Result op))
    (valid : laws.ValidObservation op observation) :
    (fromJson? (toJson observation) : Except String (ToolObservation (app.Result op))) = .ok observation := by
  have resultCodec (value : app.Result op) (h : laws.ValidResult op value) :
      (fromJson? (toJson value) : Except String (app.Result op)) = .ok value :=
    laws.result_roundtrip op value validOp h
  have optionCodec (value : Option (app.Result op)) (h : ∀ x ∈ value, laws.ValidResult op x) :
      (fromJson? (toJson value) : Except String (Option (app.Result op))) = .ok value :=
    optional_roundtrip value (fun x member => resultCodec x (h x member))
      (fun x member => laws.result_not_null op x (h x member))
  cases observation with
  | success value =>
    have fields : Json.parseCtorFields (Json.mkObj [("success", Json.mkObj [("result", toJson value)])]) "success" 1 (some #[`result]) = .ok #[toJson value] := by
      change (#[`result].mapM (fun x => (Json.mkObj [("result", toJson value)]).getObjVal? x.getString!)) = _
      simp [Array.mapM_eq_mapM_toList]
      rfl
    change (instFromJsonToolObservation.fromJson (Json.mkObj [("success", Json.mkObj [("result", toJson value)])])) = _
    simp only [instFromJsonToolObservation.fromJson, tag_singleton]
    rw [fields]
    change ((fromJson? (toJson value) : Except String (app.Result op)) >>= fun x => pure (ToolObservation.success x)) = _
    rw [resultCodec value valid]
    rfl
  | failure message =>
    have fields : Json.parseCtorFields (Json.mkObj [("failure", Json.mkObj [("message", toJson message)])]) "failure" 1 (some #[`message]) = .ok #[toJson message] := by
      change (#[`message].mapM (fun x => (Json.mkObj [("message", toJson message)]).getObjVal? x.getString!)) = _
      simp [Array.mapM_eq_mapM_toList]
      rfl
    change (instFromJsonToolObservation.fromJson (Json.mkObj [("failure", Json.mkObj [("message", toJson message)])])) = _
    simp only [instFromJsonToolObservation.fromJson, tag_singleton]
    rw [fields]
    rfl
  | timedOut output =>
    have fields : Json.parseCtorFields (Json.mkObj [("timedOut", Json.mkObj [("partialResult", toJson output)])]) "timedOut" 1 (some #[`partialResult]) = .ok #[toJson output] := by
      change (#[`partialResult].mapM (fun x => (Json.mkObj [("partialResult", toJson output)]).getObjVal? x.getString!)) = _
      simp [Array.mapM_eq_mapM_toList]
      rfl
    change (instFromJsonToolObservation.fromJson (Json.mkObj [("timedOut", Json.mkObj [("partialResult", toJson output)])])) = _
    simp only [instFromJsonToolObservation.fromJson, tag_singleton]
    rw [fields]
    change ((fromJson? (toJson output) : Except String (Option (app.Result op))) >>= fun x => pure (ToolObservation.timedOut x)) = _
    rw [optionCodec output valid]
    rfl
  | interrupted message output =>
    have fields : Json.parseCtorFields (Json.mkObj [("interrupted", Json.mkObj [("message", toJson message), ("partialResult", toJson output)])]) "interrupted" 2 (some #[`message, `partialResult]) = .ok #[toJson message, toJson output] := by
      change (#[`message, `partialResult].mapM (fun x => (Json.mkObj [("message", toJson message), ("partialResult", toJson output)]).getObjVal? x.getString!)) = _
      simp [Array.mapM_eq_mapM_toList]
      rfl
    change (instFromJsonToolObservation.fromJson (Json.mkObj [("interrupted", Json.mkObj [("message", toJson message), ("partialResult", toJson output)])])) = _
    simp only [instFromJsonToolObservation.fromJson, tag_singleton]
    rw [fields]
    change ((fromJson? (toJson output) : Except String (Option (app.Result op))) >>= fun x => pure (ToolObservation.interrupted message x)) = _
    rw [optionCodec output valid]
    rfl
  | uncertain message output =>
    have fields : Json.parseCtorFields (Json.mkObj [("uncertain", Json.mkObj [("message", toJson message), ("partialResult", toJson output)])]) "uncertain" 2 (some #[`message, `partialResult]) = .ok #[toJson message, toJson output] := by
      change (#[`message, `partialResult].mapM (fun x => (Json.mkObj [("message", toJson message), ("partialResult", toJson output)]).getObjVal? x.getString!)) = _
      simp [Array.mapM_eq_mapM_toList]
      rfl
    change (instFromJsonToolObservation.fromJson (Json.mkObj [("uncertain", Json.mkObj [("message", toJson message), ("partialResult", toJson output)])])) = _
    simp only [instFromJsonToolObservation.fromJson, tag_singleton]
    rw [fields]
    change ((fromJson? (toJson output) : Except String (Option (app.Result op))) >>= fun x => pure (ToolObservation.uncertain message x)) = _
    rw [optionCodec output valid]
    rfl

/-- The JSON completion consumed by replay is the same typed tool response. -/
theorem application_tool_reply_roundtrip (laws : ApplicationLaws app) (call : Call app)
    (validOp : laws.ValidOperation call.operation)
    (observation : ToolObservation (app.Result call.operation))
    (valid : laws.ValidObservation call.operation observation) :
    replyFromJson (.tool call) (replyToJson (.tool call) observation) = .ok observation :=
  application_observation_roundtrip laws call.operation validOp observation valid

end Harness
