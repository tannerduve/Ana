import Harness.Core.Policy
import Harness.Proofs.Except

/-! Contracts for the executable whole-batch validator. One fold induction proves
ordered call identity, freshness and uniqueness; length preservation follows from
that ordered identity result. No tools are dispatched by these definitions. -/

namespace Harness

variable {app : Application}
open ExceptRules

theorem decoded_call_identity (raw : RawCall) (call : (Call app))
    (accepted : decodeCall raw app = .ok call) : call.id = raw.id := by
  by_cases empty : raw.id = ""
  · simp [decodeCall, empty] at accepted
  · cases decoded : app.decode raw <;> simp [decodeCall, empty, decoded] at accepted
    cases accepted
    rfl

private def validationFold (state : List String × List (Call app)) (raw : RawCall) :
    Except String (List String × List (Call app)) := do
  if state.1.contains raw.id then throw "duplicate tool call identity"
  let call ← decodeCall raw app
  return (raw.id :: state.1, state.2 ++ [call])

private theorem validationFold_eq : validationFold = (fun (ids, acc) raw => do
    if ids.contains raw.id then throw "duplicate tool call identity"
    let call ← decodeCall raw app
    pure (raw.id :: ids, acc ++ [call])) := by
  funext state raw
  cases state
  rfl

private theorem validation_fold_ids (raws : List RawCall)
    (ids : List String) (acc : List (Call app)) (outIds : List String) (result : List (Call app))
    (accepted : raws.foldlM validationFold (ids, acc) = .ok (outIds, result)) :
    result.map (·.id) = acc.map (·.id) ++ raws.map (·.id) ∧
    (raws.map (·.id)).Nodup ∧ ∀ id ∈ raws.map (·.id), id ∉ ids := by
  induction raws generalizing ids acc with
  | nil =>
    simp only [List.foldlM_nil, pure_ok, Except.ok.injEq, Prod.mk.injEq] at accepted
    rcases accepted with ⟨_, rfl⟩
    simp
  | cons raw tail ih =>
    simp only [List.foldlM_cons] at accepted
    by_cases duplicate : raw.id ∈ ids
    · simp [validationFold, duplicate] at accepted
    · cases decoded : decodeCall raw app with
      | error message => simp [validationFold, duplicate, decoded] at accepted
      | ok call =>
        have remaining : tail.foldlM validationFold (raw.id :: ids, acc ++ [call]) =
            .ok (outIds, result) := by
          simpa [validationFold, duplicate, decoded] using accepted
        obtain ⟨equal, distinct, fresh⟩ := ih (raw.id :: ids) (acc ++ [call]) remaining
        have identity := decoded_call_identity raw call decoded
        constructor
        · simpa [List.map_append, identity, List.append_assoc] using equal
        constructor
        · simp only [List.map_cons, List.nodup_cons]
          exact ⟨fun member => fresh raw.id member (by simp), distinct⟩
        · intro id member
          simp only [List.map_cons, List.mem_cons] at member
          rcases member with rfl | member
          · exact duplicate
          · intro previous
            exact fresh id member (by simp [previous])

/-- Successful whole-batch validation preserves IDs in order and forbids both
within-batch duplication and reuse of any previously admitted call identity. -/
theorem validated_batch_ids (config : Config) (seen : List String)
    (raws : List RawCall) (calls : List (Call app))
    (accepted : validateBatch config seen raws app = .ok calls) :
    calls.map (·.id) = raws.map (·.id) ∧
    (calls.map (·.id)).Nodup ∧ ∀ id ∈ calls.map (·.id), id ∉ seen := by
  by_cases empty : raws.isEmpty = true
  · simp [validateBatch, empty] at accepted
  · by_cases oversized : raws.length > config.maxBatchCalls
    · simp [validateBatch, empty, oversized] at accepted
    · have folded : (do
          let pair ← raws.foldlM validationFold (seen, [])
          pure pair.2) = (Except.ok calls : Except String (List (Call app))) := by
        rw [validationFold_eq]
        simpa [validateBatch, empty, oversized] using accepted
      cases hf : raws.foldlM (validationFold (app := app)) (seen, []) with
      | error message => simp [hf] at folded
      | ok pair =>
        obtain ⟨ids, admitted⟩ := pair
        simp only [hf, ok_bind, pure_ok, Except.ok.injEq] at folded
        subst admitted
        obtain ⟨equal, distinct, fresh⟩ := validation_fold_ids raws seen [] ids calls hf
        simp only [List.map_nil, List.nil_append] at equal
        exact ⟨equal, equal ▸ distinct, equal ▸ fresh⟩

/-- The typed batch preserves the raw length and obeys the configured bound. -/
theorem validated_batch_length (config : Config) (seen : List String)
    (raws : List RawCall) (calls : List (Call app))
    (accepted : validateBatch config seen raws app = .ok calls) :
    calls.length = raws.length ∧ calls.length ≤ config.maxBatchCalls := by
  have same : calls.length = raws.length := by
    simpa using congrArg List.length (validated_batch_ids config seen raws calls accepted).1
  refine ⟨same, ?_⟩
  by_cases empty : raws.isEmpty = true
  · simp [validateBatch, empty] at accepted
  · by_cases oversized : raws.length > config.maxBatchCalls
    · simp [validateBatch, empty, oversized] at accepted
    · exact same ▸ Nat.le_of_not_gt oversized

/-- Every successful decoder-level predicate lifts through the real whole-batch
validator, independently of its argument parser or result encoder. -/
theorem validated_batch_all (property : (Call app) → Prop)
    (decoded : ∀ raw call, decodeCall raw app = .ok call → property call)
    (config : Config) (seen : List String) (raws : List RawCall) (calls : List (Call app))
    (accepted : validateBatch config seen raws app = .ok calls) :
    ∀ call ∈ calls, property call := by
  let next := fun (state : List String × List (Call app)) (raw : RawCall) => do
    if state.1.contains raw.id then throw "duplicate tool call identity"
    let call ← decodeCall raw app
    pure (raw.id :: state.1, state.2 ++ [call])
  have folded : ExceptSuccess (fun result : List String × List (Call app) =>
      ∀ call ∈ result.2, property call) (raws.foldlM next (seen, [])) := by
    intro result acceptedFold
    apply ExceptSuccess.foldlM_preserves (fun result => ∀ call ∈ result.2, property call)
      next raws (seen, []) result (by simp) ?_ acceptedFold
    intro raw _ before after valid stepAccepted
    dsimp only [next] at stepAccepted
    by_cases duplicate : raw.id ∈ before.1
    · simp [duplicate] at stepAccepted
    · simp only [List.contains_iff_mem, duplicate, if_false] at stepAccepted
      obtain ⟨call, parsed, final⟩ := ExceptSuccess.bind_ok_exists _ _ _ stepAccepted
      simp only [pure_ok, Except.ok.injEq] at final
      subst after
      intro proposed member
      rcases List.mem_append.mp member with old | single
      · exact valid proposed old
      · have equal : proposed = call := by simpa using single
        exact equal ▸ decoded raw call parsed
  have next_eq : next = (fun (ids, acc) raw => do
      if ids.contains raw.id then throw "duplicate tool call identity"
      let call ← decodeCall raw app
      pure (raw.id :: ids, acc ++ [call])) := by
    funext state raw
    cases state
    rfl
  by_cases empty : raws.isEmpty = true
  · simp [validateBatch, empty] at accepted
  · by_cases large : raws.length > config.maxBatchCalls
    · simp [validateBatch, empty, large] at accepted
    · simp only [validateBatch, empty, large, ↓reduceIte] at accepted
      rw [← next_eq] at accepted
      obtain ⟨result, parsed, final⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
      simp only [pure_ok, Except.ok.injEq] at final
      exact final ▸ folded result parsed

end Harness
