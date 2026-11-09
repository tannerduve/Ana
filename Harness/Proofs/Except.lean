import Mathlib.Control.Monad.Basic
import Mathlib.Data.List.Basic

/-! Shared reasoning about successful `Except` results. Failures impose no
postcondition. These lemmas describe the existing `Except` and `List.foldlM`
operations; they do not implement a second parser or replay loop. -/

namespace Harness

namespace ExceptRules

@[simp] theorem ok_bind {ε α β : Type} (value : α) (next : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= next) = next value := rfl
@[simp] theorem error_bind {ε α β : Type} (error : ε) (next : α → Except ε β) :
    ((Except.error error : Except ε α) >>= next) = .error error := rfl
@[simp] theorem pure_ok {ε α : Type} (value : α) :
    (pure value : Except ε α) = .ok value := rfl
@[simp] theorem throw_error {ε α : Type} (error : ε) :
    (throw error : Except ε α) = .error error := rfl

end ExceptRules

/-- Every successful result satisfies the predicate; errors are unrestricted. -/
def ExceptSuccess {ε α : Type} (property : α → Prop) (result : Except ε α) : Prop :=
  ∀ value, result = .ok value → property value

namespace ExceptSuccess
open ExceptRules

theorem error_iff {ε α : Type} (property : α → Prop) (message : ε) :
    ExceptSuccess property (.error message) ↔ True := by simp [ExceptSuccess]

theorem ok_iff {ε α : Type} (property : α → Prop) (value : α) :
    ExceptSuccess property (.ok value : Except ε α) ↔ property value := by
  simp [ExceptSuccess]

theorem bind {ε α β : Type} (property : β → Prop) (source : Except ε α)
    (next : α → Except ε β) (valid : ∀ value, ExceptSuccess property (next value)) :
    ExceptSuccess property (source >>= next) := by
  cases source with
  | error message => intro value impossible; cases impossible
  | ok value => exact valid value

theorem if_iff {ε α : Type} (property : α → Prop) (condition : Prop) [Decidable condition]
    (yes no : Except ε α) :
    ExceptSuccess property (if condition then yes else no) ↔
      (condition → ExceptSuccess property yes) ∧ (¬condition → ExceptSuccess property no) := by
  by_cases h : condition <;> simp [h]

theorem bind_iff {ε α β : Type} (property : β → Prop) (source : Except ε α)
    (next : α → Except ε β) :
    ExceptSuccess property (source >>= next) ↔
      ∀ value, source = .ok value → ExceptSuccess property (next value) := by
  cases source <;> simp [ExceptSuccess]

theorem bind_ok_exists {ε α β : Type} (source : Except ε α)
    (next : α → Except ε β) (result : β) (accepted : (source >>= next) = .ok result) :
    ∃ value, source = .ok value ∧ next value = .ok result := by
  cases source with
  | error message => simp at accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- A successful fold preserves an invariant when each accepted item does.
The membership premise permits contracts restricted to this particular input. -/
theorem foldlM_preserves {ε α β : Type} (property : β → Prop)
    (next : β → α → Except ε β) (items : List α) (first last : β)
    (initial : property first)
    (preserves : ∀ item ∈ items, ∀ before after,
      property before → next before item = .ok after → property after)
    (accepted : items.foldlM next first = .ok last) : property last := by
  induction items generalizing first with
  | nil =>
    simp only [List.foldlM_nil, pure_ok, Except.ok.injEq] at accepted
    exact accepted ▸ initial
  | cons item rest ih =>
    simp only [List.foldlM_cons] at accepted
    obtain ⟨middle, head, tail⟩ := bind_ok_exists _ _ _ accepted
    exact ih middle (preserves item (by simp) first middle initial head)
      (fun item member => preserves item (by simp [member])) tail

end ExceptSuccess
end Harness
