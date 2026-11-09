import Harness.Core.ApplicationLaws
import Harness.Proofs.Except
import Std.Data.TreeMap.Raw.Lemmas

/-! Kernel-checked laws for the actual Lean JSON instances used by the application boundary.
These are JSON-value laws, not claims about arbitrary textual JSON or the OS journal adapter. -/
namespace Harness.ApplicationCodec
open Lean
open ExceptRules

@[simp] theorem tag_singleton (tag : String) (value : Json) :
    Json.getTag? (Json.mkObj [(tag, value)]) = some tag := by
  have hm : ((∅ : Std.TreeMap.Raw String Json compare).insert tag value).minKey? = some tag :=
    Std.TreeMap.Raw.minKey?_insert_of_isEmpty Std.TreeMap.Raw.WF.empty (by rfl)
  change (guard (true = true) *> ((∅ : Std.TreeMap.Raw String Json compare).insert tag value).minKey?) = _
  rw [hm]
  rfl

@[simp] theorem string_roundtrip (value : String) :
    (fromJson? (toJson value) : Except String String) = .ok value := rfl
@[simp] theorem nat_roundtrip (value : Nat) :
    (fromJson? (toJson value) : Except String Nat) = .ok value := rfl
@[simp] theorem bool_roundtrip (value : Bool) :
    (fromJson? (toJson value) : Except String Bool) = .ok value := rfl
@[simp] theorem int_roundtrip (value : Int) :
    (fromJson? (toJson value) : Except String Int) = .ok value := by cases value <;> rfl

@[simp] theorem option_int_roundtrip (value : Option Int) :
    (fromJson? (toJson value) : Except String (Option Int)) = .ok value := by
  cases value with
  | none => rfl
  | some value => cases value <;> rfl
@[simp] theorem option_string_roundtrip (value : Option String) :
    (fromJson? (toJson value) : Except String (Option String)) = .ok value := by cases value <;> rfl
@[simp] theorem option_nat_roundtrip (value : Option Nat) :
    (fromJson? (toJson value) : Except String (Option Nat)) = .ok value := by cases value <;> rfl

theorem mapM_encode {α β ε : Type} (encode : α → β) (decode : β → Except ε α)
    (values : Array α) (roundtrip : ∀ value ∈ values, decode (encode value) = .ok value) :
    (values.map encode).mapM decode = .ok values := by
  rw [Array.mapM_map]
  rcases values with ⟨values⟩
  simp only [List.mem_toArray] at roundtrip
  suffices h : values.mapM (decode ∘ encode) = (Except.ok values : Except ε (List α)) by
    simpa using congrArg (Functor.map List.toArray) h
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp [List.mapM_cons, roundtrip value (by simp), ih (fun x hx => roundtrip x (by simp [hx]))]

theorem array_roundtrip {α : Type} [ToJson α] [FromJson α] (values : Array α)
    (roundtrip : ∀ value ∈ values, (fromJson? (toJson value) : Except String α) = .ok value) :
    (fromJson? (toJson values) : Except String (Array α)) = .ok values :=
  mapM_encode toJson fromJson? values roundtrip

@[simp] theorem string_array_roundtrip (values : Array String) :
    (fromJson? (toJson values) : Except String (Array String)) = .ok values :=
  array_roundtrip values (fun _ _ => string_roundtrip _)

theorem optional_roundtrip {α : Type} [ToJson α] [FromJson α] (value : Option α)
    (roundtrip : ∀ item ∈ value, (fromJson? (toJson item) : Except String α) = .ok item)
    (nonnull : ∀ item ∈ value, toJson item ≠ Json.null) :
    (fromJson? (toJson value) : Except String (Option α)) = .ok value := by
  cases value with
  | none => rfl
  | some item =>
    have h := roundtrip item (by simp)
    have hn := nonnull item (by simp)
    change Lean.Option.fromJson? (toJson item) = _
    cases encoded : toJson item <;> simp only [Lean.Option.fromJson?]
    · exact False.elim (hn encoded)
    all_goals rw [← encoded, h]; rfl

end Harness.ApplicationCodec
