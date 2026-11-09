import Harness.Core.Coding
import Harness.Proofs.ApplicationCodec

/-! The coding contract is about lexical arguments and typed metadata. Physical path containment,
process settlement, file identities and the truth of observations remain adapter obligations. -/
namespace Harness.Coding
open Lean ApplicationCodec ExceptRules

/-- Independent admissibility predicates for coding arguments. These inspect fields, not codecs. -/
def ValidOperation : ToolOp → Prop
  | .listFiles a => safePath a.path = true ∧ 0 < a.limit ∧ a.limit ≤ 2000
  | .readFile a => safePath a.path = true ∧ 0 < a.startLine ∧ a.startLine ≤ a.endLine ∧ a.endLine - a.startLine ≤ 2000
  | .searchFiles a => safePath a.path = true ∧ a.query ≠ "" ∧ 0 < a.limit ∧ a.limit ≤ 2000
  | .editFile a => safePath a.path = true ∧ a.old ≠ "" ∧ a.expectedSha256.length = 64
  | .createFile a => safePath a.path = true
  | .runProcess a => safePath a.cwd = true ∧ a.argv.isEmpty = false ∧ a.argv[0]! ≠ ""
  | .readArtifact a => a.id ≠ "" ∧ a.id.length ≤ 80 ∧ 0 < a.length ∧ a.length ≤ 65536

/-- Paths that the operation supplies to the coding interpreter. Artifact IDs are not paths. -/
def operationPaths : ToolOp → List String
  | .listFiles a => [a.path]
  | .readFile a => [a.path]
  | .searchFiles a => [a.path]
  | .editFile a => [a.path]
  | .createFile a => [a.path]
  | .runProcess a => [a.cwd]
  | .readArtifact _ => []

theorem valid_operation_paths (op : ToolOp) (valid : ValidOperation op) :
    ∀ path ∈ operationPaths op, safePath path = true := by
  cases op <;> simp_all [ValidOperation, operationPaths]

/-- Metadata admissibility does not certify file contents, process exit, or external effects.
The universal codec law below also covers invalid metadata, so the core can reject it faithfully. -/
def ValidResult (_ : ToolOp) (result : ToolResult) : Prop :=
  (∀ code ∈ result.exitCode, 0 ≤ code ∧ code ≤ 255) ∧
  (∀ hash ∈ result.sha256, hash.length = 64) ∧
  ∀ ref ∈ result.artifacts, ref.id ≠ "" ∧ ref.sha256.length = 64 ∧
    ref.storedBytes ≤ ref.totalBytes

theorem validated_operation_valid (op : ToolOp) (accepted : validateOperation op = .ok ()) :
    ValidOperation op := by
  cases op <;> simp_all [validateOperation, ValidOperation, String.isEmpty_iff]
  all_goals omega

theorem decode_valid (raw : RawCall) : ExceptSuccess ValidOperation (decodeOperation raw) := by
  intro op accepted
  obtain ⟨parsed, _, checked⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
  obtain ⟨result, valid, returned⟩ := ExceptSuccess.bind_ok_exists _ _ _ checked
  cases result
  cases returned
  exact validated_operation_valid _ valid

@[simp] theorem list_args_roundtrip (value : ListArgs) :
    (fromJson? (toJson value) : Except String ListArgs) = .ok value := by cases value; rfl
@[simp] theorem read_args_roundtrip (value : ReadArgs) :
    (fromJson? (toJson value) : Except String ReadArgs) = .ok value := by cases value; rfl
@[simp] theorem search_args_roundtrip (value : SearchArgs) :
    (fromJson? (toJson value) : Except String SearchArgs) = .ok value := by cases value; rfl
@[simp] theorem edit_args_roundtrip (value : EditArgs) :
    (fromJson? (toJson value) : Except String EditArgs) = .ok value := by cases value; rfl
@[simp] theorem create_args_roundtrip (value : CreateArgs) :
    (fromJson? (toJson value) : Except String CreateArgs) = .ok value := by cases value; rfl
@[simp] theorem artifact_args_roundtrip (value : ArtifactReadArgs) :
    (fromJson? (toJson value) : Except String ArtifactReadArgs) = .ok value := by cases value; rfl
@[simp] theorem process_args_roundtrip (value : ProcessArgs) :
    (fromJson? (toJson value) : Except String ProcessArgs) = .ok value := by
  change (do
    let argv ← Except.mapError _ (fromJson? (toJson value.argv))
    let cwd ← Except.mapError _ (.ok value.cwd : Except String String)
    pure (ProcessArgs.mk argv cwd)) = .ok value
  rw [string_array_roundtrip]
  rfl

theorem operation_roundtrip (op : ToolOp) :
    (fromJson? (toJson op) : Except String ToolOp) = .ok op := by
  cases op with
  | listFiles a =>
    have fields : Json.parseCtorFields (Json.mkObj [("listFiles", Json.mkObj [("args", toJson a)])])
        "listFiles" 1 (some #[`args]) = .ok #[toJson a] := by
      change (#[`args].mapM (fun x => (Json.mkObj [("args", toJson a)]).getObjVal? x.getString!)) = _
      simp [Array.mapM_eq_mapM_toList]
      rfl
    change (instFromJsonToolOp.fromJson (Json.mkObj [("listFiles", Json.mkObj [("args", toJson a)])])) = _
    simp only [instFromJsonToolOp.fromJson, tag_singleton]
    rw [fields]
    change ((fromJson? (toJson a) : Except String ListArgs) >>= fun x => pure (ToolOp.listFiles x)) = _
    rw [list_args_roundtrip]
    rfl
  | readFile a =>
    have fields : Json.parseCtorFields (Json.mkObj [("readFile", Json.mkObj [("args", toJson a)])])
        "readFile" 1 (some #[`args]) = .ok #[toJson a] := by
      change (#[`args].mapM (fun x => (Json.mkObj [("args", toJson a)]).getObjVal? x.getString!)) = _
      simp [Array.mapM_eq_mapM_toList]
      rfl
    change (instFromJsonToolOp.fromJson (Json.mkObj [("readFile", Json.mkObj [("args", toJson a)])])) = _
    simp only [instFromJsonToolOp.fromJson, tag_singleton]
    rw [fields]
    change ((fromJson? (toJson a) : Except String ReadArgs) >>= fun x => pure (ToolOp.readFile x)) = _
    rw [read_args_roundtrip]
    rfl
  | searchFiles a =>
    have fields : Json.parseCtorFields (Json.mkObj [("searchFiles", Json.mkObj [("args", toJson a)])])
        "searchFiles" 1 (some #[`args]) = .ok #[toJson a] := by
      change (#[`args].mapM (fun x => (Json.mkObj [("args", toJson a)]).getObjVal? x.getString!)) = _
      simp [Array.mapM_eq_mapM_toList]
      rfl
    change (instFromJsonToolOp.fromJson (Json.mkObj [("searchFiles", Json.mkObj [("args", toJson a)])])) = _
    simp only [instFromJsonToolOp.fromJson, tag_singleton]
    rw [fields]
    change ((fromJson? (toJson a) : Except String SearchArgs) >>= fun x => pure (ToolOp.searchFiles x)) = _
    rw [search_args_roundtrip]
    rfl
  | editFile a =>
    have fields : Json.parseCtorFields (Json.mkObj [("editFile", Json.mkObj [("args", toJson a)])])
        "editFile" 1 (some #[`args]) = .ok #[toJson a] := by
      change (#[`args].mapM (fun x => (Json.mkObj [("args", toJson a)]).getObjVal? x.getString!)) = _
      simp [Array.mapM_eq_mapM_toList]
      rfl
    change (instFromJsonToolOp.fromJson (Json.mkObj [("editFile", Json.mkObj [("args", toJson a)])])) = _
    simp only [instFromJsonToolOp.fromJson, tag_singleton]
    rw [fields]
    change ((fromJson? (toJson a) : Except String EditArgs) >>= fun x => pure (ToolOp.editFile x)) = _
    rw [edit_args_roundtrip]
    rfl
  | createFile a =>
    have fields : Json.parseCtorFields (Json.mkObj [("createFile", Json.mkObj [("args", toJson a)])])
        "createFile" 1 (some #[`args]) = .ok #[toJson a] := by
      change (#[`args].mapM (fun x => (Json.mkObj [("args", toJson a)]).getObjVal? x.getString!)) = _
      simp [Array.mapM_eq_mapM_toList]
      rfl
    change (instFromJsonToolOp.fromJson (Json.mkObj [("createFile", Json.mkObj [("args", toJson a)])])) = _
    simp only [instFromJsonToolOp.fromJson, tag_singleton]
    rw [fields]
    change ((fromJson? (toJson a) : Except String CreateArgs) >>= fun x => pure (ToolOp.createFile x)) = _
    rw [create_args_roundtrip]
    rfl
  | runProcess a =>
    have fields : Json.parseCtorFields (Json.mkObj [("runProcess", Json.mkObj [("args", toJson a)])])
        "runProcess" 1 (some #[`args]) = .ok #[toJson a] := by
      change (#[`args].mapM (fun x => (Json.mkObj [("args", toJson a)]).getObjVal? x.getString!)) = _
      simp [Array.mapM_eq_mapM_toList]
      rfl
    change (instFromJsonToolOp.fromJson (Json.mkObj [("runProcess", Json.mkObj [("args", toJson a)])])) = _
    simp only [instFromJsonToolOp.fromJson, tag_singleton]
    rw [fields]
    change ((fromJson? (toJson a) : Except String ProcessArgs) >>= fun x => pure (ToolOp.runProcess x)) = _
    rw [process_args_roundtrip]
    rfl
  | readArtifact a =>
    have fields : Json.parseCtorFields (Json.mkObj [("readArtifact", Json.mkObj [("args", toJson a)])])
        "readArtifact" 1 (some #[`args]) = .ok #[toJson a] := by
      change (#[`args].mapM (fun x => (Json.mkObj [("args", toJson a)]).getObjVal? x.getString!)) = _
      simp [Array.mapM_eq_mapM_toList]
      rfl
    change (instFromJsonToolOp.fromJson (Json.mkObj [("readArtifact", Json.mkObj [("args", toJson a)])])) = _
    simp only [instFromJsonToolOp.fromJson, tag_singleton]
    rw [fields]
    change ((fromJson? (toJson a) : Except String ArtifactReadArgs) >>= fun x => pure (ToolOp.readArtifact x)) = _
    rw [artifact_args_roundtrip]
    rfl

@[simp] theorem artifact_ref_roundtrip (value : ArtifactRef) :
    (fromJson? (toJson value) : Except String ArtifactRef) = .ok value := by cases value; rfl

theorem result_roundtrip (value : ToolResult) :
    (fromJson? (toJson value) : Except String ToolResult) = .ok value := by
  change (do
    let exitCode ← Except.mapError _ (fromJson? (toJson value.exitCode) : Except String (Option Int))
    let artifacts ← Except.mapError _ (fromJson? (toJson value.artifacts) : Except String (Array ArtifactRef))
    let sha256 ← Except.mapError _ (fromJson? (toJson value.sha256) : Except String (Option String))
    pure (ToolResult.mk value.text exitCode artifacts sha256)) = .ok value
  rw [option_int_roundtrip, array_roundtrip value.artifacts (fun _ _ => artifact_ref_roundtrip _),
    option_string_roundtrip]
  rfl

/-- Coding renders the actual typed observation without changing any field. -/
def laws : ApplicationLaws application where
  ValidOperation := ValidOperation
  ValidResult := ValidResult
  decode_valid := decode_valid
  operation_roundtrip := fun op _ => operation_roundtrip op
  result_roundtrip := fun _ result _ _ => result_roundtrip result
  result_not_null := fun _ _ _ => by intro impossible; cases impossible
  Rendered := fun _ result visible => visible = result
  render_faithful := fun _ _ _ _ => rfl

end Harness.Coding
