import Harness.Applications.Matrix
import Harness.Proofs.ApplicationCoding

namespace Harness.Matrix
open Lean ApplicationCodec ExceptRules
set_option maxHeartbeats 4000000

/-- Field predicates, independent of the model decoder and journal codec. -/
def validOperation : Operation → Bool
  | .coding op => match op with
    | .listFiles a => Coding.safePath a.path && 0 < a.limit && a.limit ≤ 2000
    | .readFile a => Coding.safePath a.path && 0 < a.startLine && a.startLine ≤ a.endLine && a.endLine - a.startLine ≤ 2000
    | .searchFiles a => Coding.safePath a.path && !a.query.isEmpty && 0 < a.limit && a.limit ≤ 2000
    | .editFile a => Coding.safePath a.path && !a.old.isEmpty && a.expectedSha256.length == 64
    | .createFile a => Coding.safePath a.path
    | .runProcess a => Coding.safePath a.cwd && !a.argv.isEmpty && !a.argv[0]!.isEmpty
    | .readArtifact a => !a.id.isEmpty && a.id.length ≤ 80 && 0 < a.length && a.length ≤ 65536
  | .lakeBuild a => a.wait_timeout_seconds.all validSeconds &&
    if a.action == .submit then a.build_id.isNone &&
      a.project.all (fun p => Coding.safePath p && p.length ≤ 256) &&
      a.build_timeout_seconds.all (fun s => 60 ≤ s && s ≤ 7200) &&
      a.cpus.all (fun c => 1 ≤ c && c ≤ 30) && a.memory_gb.all validMemory && a.cache_from.all (validHex 16)
    else a.build_id.any (validHex 16) && a.project.isNone && a.wait.isNone &&
      a.build_timeout_seconds.isNone && a.cpus.isNone && a.memory_gb.isNone &&
      a.cache.isNone && a.reuse_cache.isNone && a.cache_from.isNone
  | .submit kind payload => !payload.trimAscii.toString.isEmpty && payload.utf8ByteSize ≤ kind.maxBytes

theorem validated_operation_valid (op : Operation) (accepted : validateOperation op = .ok ()) :
    validOperation op = true := by
  cases op with
  | coding op =>
    have valid := Coding.validated_operation_valid op accepted
    cases op <;> simp_all [validOperation, Coding.ValidOperation]
  | lakeBuild a =>
    by_cases submit : a.action == .submit
    all_goals simp_all [validateOperation, validateBuildArgs, validOperation]
    all_goals repeat first | (split at accepted) | (solve | simp_all)
  | submit kind payload => simp_all [validateOperation, validOperation]

theorem decode_valid (raw : RawCall) : ExceptSuccess (fun op => validOperation op = true) (decodeOperation raw) := by
  intro op accepted
  unfold decodeOperation at accepted
  obtain ⟨parsed, _, checked⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
  obtain ⟨result, valid, returned⟩ := ExceptSuccess.bind_ok_exists _ _ _ checked
  cases result
  cases returned
  exact validated_operation_valid _ valid

@[simp] theorem build_action_roundtrip (value : BuildAction) :
    (fromJson? (toJson value) : Except String BuildAction) = .ok value := by cases value <;> rfl
@[simp] theorem submission_kind_roundtrip (value : SubmissionKind) :
    (fromJson? (toJson value) : Except String SubmissionKind) = .ok value := by cases value <;> rfl
@[simp] theorem identity_roundtrip (value : Identity) :
    (fromJson? (toJson value) : Except String Identity) = .ok value := by cases value; rfl
@[simp] theorem optional_bool_roundtrip (value : Option Bool) :
    (fromJson? (toJson value) : Except String (Option Bool)) = .ok value := by cases value <;> rfl
@[simp] theorem optional_number_roundtrip (value : Option JsonNumber) :
    (fromJson? (toJson value) : Except String (Option JsonNumber)) = .ok value := by cases value <;> rfl

theorem build_args_roundtrip (value : BuildArgs) :
    (fromJson? (toJson value) : Except String BuildArgs) = .ok value := by
  change (do
    let action ← Except.mapError _ (fromJson? (toJson value.action) : Except String BuildAction)
    let project ← Except.mapError _ (fromJson? (toJson value.project) : Except String (Option String))
    let build ← Except.mapError _ (fromJson? (toJson value.build_id) : Except String (Option String))
    let wait ← Except.mapError _ (fromJson? (toJson value.wait) : Except String (Option Bool))
    let waitSeconds ← Except.mapError _ (fromJson? (toJson value.wait_timeout_seconds) : Except String (Option JsonNumber))
    let buildSeconds ← Except.mapError _ (fromJson? (toJson value.build_timeout_seconds) : Except String (Option Nat))
    let cpus ← Except.mapError _ (fromJson? (toJson value.cpus) : Except String (Option Nat))
    let memory ← Except.mapError _ (fromJson? (toJson value.memory_gb) : Except String (Option JsonNumber))
    let cache ← Except.mapError _ (fromJson? (toJson value.cache) : Except String (Option Bool))
    let reuse ← Except.mapError _ (fromJson? (toJson value.reuse_cache) : Except String (Option Bool))
    let donor ← Except.mapError _ (fromJson? (toJson value.cache_from) : Except String (Option String))
    pure (BuildArgs.mk action project build wait waitSeconds buildSeconds cpus memory cache reuse donor)) = .ok value
  simp only [build_action_roundtrip, option_string_roundtrip, optional_bool_roundtrip,
    optional_number_roundtrip, option_nat_roundtrip]
  rfl

theorem operation_roundtrip (op : Operation) :
    (fromJson? (toJson op) : Except String Operation) = .ok op := by
  cases op with
  | coding op =>
    have fields : Json.parseCtorFields (Json.mkObj [("coding", Json.mkObj [("operation", toJson op)])])
        "coding" 1 (some #[`operation]) = .ok #[toJson op] := by
      change (#[`operation].mapM (fun x => (Json.mkObj [("operation", toJson op)]).getObjVal? x.getString!)) = _
      simp [Array.mapM_eq_mapM_toList]
      rfl
    change instFromJsonOperation.fromJson (Json.mkObj [("coding", Json.mkObj [("operation", toJson op)])]) = _
    simp only [instFromJsonOperation.fromJson, tag_singleton]
    rw [fields]
    change ((fromJson? (toJson op) : Except String ToolOp) >>= fun value => pure (Operation.coding value)) = _
    rw [Coding.operation_roundtrip]
    rfl
  | lakeBuild args =>
    have fields : Json.parseCtorFields (Json.mkObj [("lakeBuild", Json.mkObj [("args", toJson args)])])
        "lakeBuild" 1 (some #[`args]) = .ok #[toJson args] := by
      change (#[`args].mapM (fun x => (Json.mkObj [("args", toJson args)]).getObjVal? x.getString!)) = _
      simp [Array.mapM_eq_mapM_toList]
      rfl
    change instFromJsonOperation.fromJson (Json.mkObj [("lakeBuild", Json.mkObj [("args", toJson args)])]) = _
    simp only [instFromJsonOperation.fromJson, tag_singleton]
    rw [fields]
    change ((fromJson? (toJson args) : Except String BuildArgs) >>= fun value => pure (Operation.lakeBuild value)) = _
    rw [build_args_roundtrip]
    rfl
  | submit kind payload =>
    have fields : Json.parseCtorFields (Json.mkObj [("submit", Json.mkObj [("kind", toJson kind), ("payload", toJson payload)])])
        "submit" 2 (some #[`kind, `payload]) = .ok #[toJson kind, toJson payload] := by
      change (#[`kind, `payload].mapM (fun x => (Json.mkObj [("kind", toJson kind), ("payload", toJson payload)]).getObjVal? x.getString!)) = _
      simp [Array.mapM_eq_mapM_toList]
      rfl
    change instFromJsonOperation.fromJson (Json.mkObj [("submit", Json.mkObj [("kind", toJson kind), ("payload", toJson payload)])]) = _
    simp only [instFromJsonOperation.fromJson, tag_singleton]
    rw [fields]
    change ((fromJson? (toJson kind) : Except String SubmissionKind) >>= fun value => pure (Operation.submit value payload)) = _
    rw [submission_kind_roundtrip]
    rfl

theorem build_receipt_roundtrip (value : BuildReceipt) :
    (fromJson? (toJson value) : Except String BuildReceipt) = .ok value := by
  change (do
    let identity ← Except.mapError (fun error => toString `Harness.Matrix.BuildReceipt ++ "." ++ toString `identity ++ ": " ++ error) (fromJson? (toJson value.identity) : Except String Identity)
    let action ← Except.mapError (fun error => toString `Harness.Matrix.BuildReceipt ++ "." ++ toString `action ++ ": " ++ error) (fromJson? (toJson value.action) : Except String BuildAction)
    let scope ← Except.mapError (fun error => toString `Harness.Matrix.BuildReceipt ++ "." ++ toString `scope ++ ": " ++ error) (fromJson? (toJson value.scope) : Except String String)
    let input ← Except.mapError (fun error => toString `Harness.Matrix.BuildReceipt ++ "." ++ toString `inputDigest ++ ": " ++ error) (fromJson? (toJson value.inputDigest) : Except String (Option String))
    let upload ← Except.mapError (fun error => toString `Harness.Matrix.BuildReceipt ++ "." ++ toString `uploadDigest ++ ": " ++ error) (fromJson? (toJson value.uploadDigest) : Except String (Option String))
    let backend ← Except.mapError (fun error => toString `Harness.Matrix.BuildReceipt ++ "." ++ toString `backendBuildId ++ ": " ++ error) (fromJson? (toJson value.backendBuildId) : Except String (Option String))
    let backends ← Except.mapError (fun error => toString `Harness.Matrix.BuildReceipt ++ "." ++ toString `backendBuildIds ++ ": " ++ error) (fromJson? (toJson value.backendBuildIds) : Except String (Array String))
    let status ← Except.mapError (fun error => toString `Harness.Matrix.BuildReceipt ++ "." ++ toString `status ++ ": " ++ error) (fromJson? (toJson value.status) : Except String String)
    let settled ← Except.mapError (fun error => toString `Harness.Matrix.BuildReceipt ++ "." ++ toString `effectSettled ++ ": " ++ error) (fromJson? (toJson value.effectSettled) : Except String Bool)
    let uncertain ← Except.mapError (fun error => toString `Harness.Matrix.BuildReceipt ++ "." ++ toString `submissionUncertain ++ ": " ++ error) (fromJson? (toJson value.submissionUncertain) : Except String Bool)
    let native ← Except.mapError (fun error => toString `Harness.Matrix.BuildReceipt ++ "." ++ toString `nativeResult ++ ": " ++ error) (fromJson? (toJson value.nativeResult) : Except String String)
    let output ← Except.mapError (fun error => toString `Harness.Matrix.BuildReceipt ++ "." ++ toString `output ++ ": " ++ error) (fromJson? (toJson value.output) : Except String ToolResult)
    pure (BuildReceipt.mk identity action scope input upload backend backends status
      settled uncertain native output)) = .ok value
  simp only [identity_roundtrip, build_action_roundtrip, option_string_roundtrip, string_array_roundtrip,
    string_roundtrip, bool_roundtrip, Coding.result_roundtrip]
  rfl

theorem submission_receipt_roundtrip (value : SubmissionReceipt) :
    (fromJson? (toJson value) : Except String SubmissionReceipt) = .ok value := by
  change (do
    let identity ← Except.mapError (fun error => toString `Harness.Matrix.SubmissionReceipt ++ "." ++ toString `identity ++ ": " ++ error) (fromJson? (toJson value.identity) : Except String Identity)
    let kind ← Except.mapError (fun error => toString `Harness.Matrix.SubmissionReceipt ++ "." ++ toString `kind ++ ": " ++ error) (fromJson? (toJson value.kind) : Except String SubmissionKind)
    let payload ← Except.mapError (fun error => toString `Harness.Matrix.SubmissionReceipt ++ "." ++ toString `payload ++ ": " ++ error) (fromJson? (toJson value.payload) : Except String String)
    let native ← Except.mapError (fun error => toString `Harness.Matrix.SubmissionReceipt ++ "." ++ toString `nativeResult ++ ": " ++ error) (fromJson? (toJson value.nativeResult) : Except String String)
    let output ← Except.mapError (fun error => toString `Harness.Matrix.SubmissionReceipt ++ "." ++ toString `output ++ ": " ++ error) (fromJson? (toJson value.output) : Except String ToolResult)
    pure (SubmissionReceipt.mk identity kind payload native output)) = .ok value
  simp only [identity_roundtrip, submission_kind_roundtrip, string_roundtrip, Coding.result_roundtrip]
  rfl

def ValidResult : (op : Operation) → Result op → Prop
  | .coding op, result => Coding.ValidResult op result
  | .lakeBuild args, result => validBuildReceipt args result = true
  | .submit kind payload, result => validSubmissionReceipt kind payload result = true

theorem result_roundtrip (op : Operation) (result : Result op) (valid : ValidResult op result) :
    decodeResult op (toJson result) = .ok result := by
  cases op with
  | coding op => exact Coding.result_roundtrip result
  | lakeBuild args =>
    dsimp only [Result] at result valid ⊢
    change (do
      let receipt : BuildReceipt ← fromJson? (toJson result)
      unless validBuildReceipt args receipt do throw "build receipt does not match the admitted operation"
      pure receipt) = .ok result
    rw [build_receipt_roundtrip]
    simp only [ok_bind, ValidResult] at *
    simp [valid]
  | submit kind payload =>
    dsimp only [Result] at result valid ⊢
    change (do
      let receipt : SubmissionReceipt ← fromJson? (toJson result)
      unless validSubmissionReceipt kind payload receipt do throw "submission receipt does not match the exact operation"
      pure receipt) = .ok result
    rw [submission_receipt_roundtrip]
    simp only [ok_bind, ValidResult] at *
    simp [valid]

/-- Rendering preserves the typed output; shared normalization and artifact
retention still apply in the engine. IO evidence truth is a separate obligation. -/
def laws : ApplicationLaws application where
  ValidOperation := fun op => validOperation op = true
  ValidResult := ValidResult
  decode_valid := decode_valid
  operation_roundtrip := fun op _ => operation_roundtrip op
  result_roundtrip := fun op result _ valid => result_roundtrip op result valid
  result_not_null := by intro op result _; cases op <;> intro impossible <;> cases impossible
  Rendered := fun op result visible => match op with
    | .coding _ => visible = result
    | .lakeBuild _ => visible = result.output
    | .submit _ _ => visible = result.output
  render_faithful := by intro op result _ _; cases op <;> rfl

/-- External recovery is allowed only for settled evidence, with its original
execution/turn/operation identity. This does not prove a service told the truth. -/
theorem uncertain_receipt_cannot_claim_settlement (args : BuildArgs) (receipt : BuildReceipt)
    (valid : validBuildReceipt args receipt = true) (uncertain : receipt.submissionUncertain = true) :
    receipt.effectSettled = false := by
  simp only [validBuildReceipt, Bool.and_eq_true] at valid
  have required := valid.1.1.1.1.2
  simp_all

end Harness.Matrix
