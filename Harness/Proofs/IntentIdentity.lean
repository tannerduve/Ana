import Harness.Proofs.AdministrativeLedger
import Harness.Proofs.OperationIdentity
import Harness.Proofs.RecordFrames

/-! Fresh intent identities across the actual mixed journal parser. Completion,
recovery and resolution may refer to an existing operation; only accepted intents
reserve new dispatch identities. The suspended-state relation is the existing
exact uncertain continuation, not an assumed monotone counter or trusted snapshot.
No additional executable state or replay implementation is introduced. -/
namespace Harness.Recovery
open Lean ExceptRules
variable {app : Application}

/-- A pending intent has already used `nextId`, even before its reply advances
the state. This derived bound is only a proof device, never a stored counter. -/
def Cursor.intentFloor (cursor : Cursor app) : Nat :=
  cursor.state.nextId + if cursor.pending then 1 else 0

/-- Projection of actual intent fields. Other record kinds intentionally do not
contribute, since their IDs refer to an operation already represented by intent. -/
def intentOperationId? (record : Json) : Option Nat := do
  if (record.getObjValAs? String "kind").toOption != some "intent" then none
  else (record.getObjValAs? Nat "id").toOption

theorem checked_target_identity (config : Config) (cursor : Cursor app) (prior : State app)
    (valid : CursorCoreValid config cursor) (accepted : checkedTarget cursor = .ok prior) :
    prior.nextId + 1 = cursor.intentFloor ∧ prior.turn = cursor.state.turn := by
  by_cases pending : cursor.pending = true
  · by_cases invalid : (cursor.terminal || cursor.suspended.isSome) = true
    · simp [checkedTarget, pending, invalid] at accepted
    · have equal : cursor.state = prior := by simpa [checkedTarget, pending, invalid] using accepted
      cases equal
      simp [Cursor.intentFloor, pending]
  · cases saved : cursor.suspended with
    | none => simp [checkedTarget, pending, saved] at accepted
    | some old =>
      obtain ⟨_, response, _, current⟩ := valid.suspended old saved
      have serial := step_advances_operation_id old response
      have turn := step_preserves_turn old response
      rw [← current] at serial turn
      simp only [checkedTarget, pending, Bool.false_eq_true, ↓reduceIte, saved] at accepted
      split at accepted
      · cases action : (step old).1 <;> simp only [action] at accepted
        all_goals simp at accepted
        rw [← accepted]
        exact ⟨by simpa [Cursor.intentFloor, pending] using serial.symm, turn.symm⟩
      · simp at accepted

private def IdentityNode (prior : State app) (node : HarnessF app (State app)) : Prop :=
  ∀ response : Reply node.1, (node.2 response).nextId = prior.nextId + 1 ∧
    (node.2 response).turn = prior.turn

private theorem recovery_target_identity (cursor next : Cursor app) (prior : State app)
    (id : Nat) (disposition : Disposition) (target : checkedTarget cursor = .ok prior)
    (accepted : recover cursor id disposition = .ok next) :
    next.pending = false ∧ next.state.nextId = prior.nextId + 1 ∧
      next.state.turn = prior.turn := by
  by_cases same : id = prior.nextId
  · subst id
    cases node : step prior with
    | mk action continuation =>
      have frame : ∀ response : Reply action,
          (continuation response).nextId = prior.nextId + 1 ∧
            (continuation response).turn = prior.turn := by
        have preserved : IdentityNode prior (step prior) :=
          fun response => ⟨step_advances_operation_id prior response, step_preserves_turn prior response⟩
        rw [node] at preserved
        exact preserved
      cases action <;> cases disposition <;>
        simp only [recover, target, node, ok_bind, beq_self_eq_true,
          ↓reduceIte, pure_ok, throw_error, error_bind] at accepted
      all_goals repeat' first
        | (split at accepted)
        | (simp only [pure_ok, throw_error, ok_bind, error_bind,
            bind, Except.bind, Functor.map, Except.map] at accepted)
        | (cases accepted)
        | (exact ⟨rfl, rfl, rfl⟩)
        | (exact ⟨rfl, frame _⟩)
  · simp [recover, target, same] at accepted

theorem recovery_preserves_intent_floor (config : Config) (cursor next : Cursor app)
    (id : Nat) (disposition : Disposition) (valid : CursorCoreValid config cursor)
    (accepted : recover cursor id disposition = .ok next) :
    next.intentFloor = cursor.intentFloor ∧ next.state.turn = cursor.state.turn := by
  cases target : checkedTarget cursor with
  | error message => simp [recover, target] at accepted
  | ok prior =>
    obtain ⟨serial, turn⟩ := checked_target_identity config cursor prior valid target
    obtain ⟨pending, advanced, retained⟩ := recovery_target_identity cursor next prior id disposition target accepted
    exact ⟨by simp [Cursor.intentFloor, pending, advanced, serial], retained.trans turn⟩

theorem resolution_preserves_intent_floor (config : Config) (cursor next : Cursor app)
    (id : Nat) (resolution : app.Resolution) (valid : CursorCoreValid config cursor)
    (accepted : resolve cursor id resolution = .ok next) :
    next.intentFloor = cursor.intentFloor ∧ next.state.turn = cursor.state.turn := by
  cases target : checkedTarget cursor with
  | error message => simp [resolve, target] at accepted
  | ok prior =>
    obtain ⟨serial, turn⟩ := checked_target_identity config cursor prior valid target
    obtain ⟨response, rfl, _⟩ := resolve_continuation cursor next prior id resolution target accepted
    exact ⟨by simpa [Cursor.intentFloor, step_advances_operation_id] using serial,
      (step_preserves_turn prior response).trans turn⟩

private theorem accepted_intent_id (cursor next : Cursor app) (record : Json)
    (kind : record.getObjValAs? String "kind" = .ok "intent")
    (accepted : applyRecord cursor record = .ok next) :
    record.getObjValAs? Nat "id" = .ok cursor.state.nextId := by
  cases identifier : record.getObjValAs? Nat "id" with
  | error message => simp [applyRecord, kind, identifier] at accepted
  | ok id =>
    by_cases same : id = cursor.state.nextId
    · simp [same]
    · simp only [applyRecord, kind, identifier, ok_bind, pure_ok, throw_error, error_bind] at accepted
      simp only [show ("intent" == "recovery") = false from by decide,
        show ("intent" == "resolution") = false from by decide,
        show ("intent" == "user_turn") = false from by decide,
        Bool.false_eq_true, if_false] at accepted
      split at accepted
      · cases accepted
      · simp [same] at accepted

/-- A new intent reserves precisely the current operation identity. This is a
fact about accepted raw records, not a premise that IDs were already unique. -/
theorem accepted_intent_identity (cursor next : Cursor app) (record : Json) (id : Nat)
    (projected : intentOperationId? record = some id)
    (accepted : applyRecord cursor record = .ok next) :
    id = cursor.intentFloor ∧ next.intentFloor = id + 1 := by
  have kind : record.getObjValAs? String "kind" = .ok "intent" := by
    cases decoded : record.getObjValAs? String "kind" with
    | error message => simp [intentOperationId?, decoded, Except.toOption] at projected
    | ok name =>
      by_cases same : name = "intent"
      · simp [same]
      · simp [intentOperationId?, decoded, same, Except.toOption] at projected
  have identifier := accepted_intent_id cursor next record kind accepted
  have equal : cursor.state.nextId = id := by
    simpa [intentOperationId?, kind, identifier, Except.toOption] using projected
  obtain ⟨pending, state, afterPending⟩ := accepted_intent_frame cursor next record kind accepted
  simp [Cursor.intentFloor, pending, state, afterPending, equal]

/-- Recovery consumes the same reserved identity, including resolution of a
suspended uncertainty. No accepted record can make a used identity available. -/
theorem apply_record_intent_floor_monotone (config : Config) (cursor next : Cursor app)
    (record : Json) (valid : CursorCoreValid config cursor)
    (accepted : applyRecord cursor record = .ok next) :
    cursor.intentFloor ≤ next.intentFloor := by
  obtain ⟨kind, decoded, known⟩ := accepted_record_kind_known cursor next record accepted
  simp only [List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨pending, state, afterPending⟩ := accepted_intent_frame cursor next record decoded accepted
    simp [Cursor.intentFloor, pending, state, afterPending]
  · obtain ⟨_, response, pending, _, _, rfl⟩ := accepted_completion_frame cursor next record decoded accepted
    simp [Cursor.intentFloor, pending, complete, step_advances_operation_id]
  · obtain ⟨state, pending⟩ := accepted_terminal_frame cursor next record decoded accepted
    simp [Cursor.intentFloor, state, pending]
  · obtain ⟨id, disposition, accepted⟩ := accepted_recovery_frame cursor next record decoded accepted
    exact Nat.le_of_eq (recovery_preserves_intent_floor config cursor next id disposition valid accepted).1.symm
  · obtain ⟨id, resolution, accepted⟩ := accepted_resolution_frame cursor next record decoded accepted
    exact Nat.le_of_eq (resolution_preserves_intent_floor config cursor next id resolution valid accepted).1.symm
  · obtain ⟨id, turn, task, accepted⟩ := accepted_user_turn_frame cursor next record decoded accepted
    obtain ⟨_, pending, _, _, _, _, begun, afterPending, _⟩ := new_turn_contract cursor next id turn task accepted
    unfold Cursor.intentFloor
    rw [(begin_turn_contract cursor.state next.state task begun).1]
    simp [pending, afterPending, turnCandidate]

private theorem mixed_intents_ordered (config : Config) (first last : Cursor app)
    (records : List Json) (valid : CursorCoreValid config first)
    (accepted : records.foldlM applyRecord first = .ok last) :
    (records.filterMap intentOperationId?).Pairwise (· < ·) ∧
      ∀ id ∈ records.filterMap intentOperationId?, first.intentFloor ≤ id := by
  induction records generalizing first with
  | nil => simp
  | cons record rest ih =>
    simp only [List.foldlM_cons] at accepted
    obtain ⟨next, head, tail⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
    obtain ⟨ordered, lower⟩ := ih next (apply_record_core_valid config first next record valid head) tail
    have monotone := apply_record_intent_floor_monotone config first next record valid head
    cases projected : intentOperationId? record with
    | none =>
      simp only [List.filterMap_cons, projected]
      exact ⟨ordered, fun id member => Nat.le_trans monotone (lower id member)⟩
    | some id =>
      obtain ⟨before, after⟩ := accepted_intent_identity first next record id projected head
      simp only [List.filterMap_cons, projected, List.pairwise_cons]
      refine ⟨⟨?_, ordered⟩, ?_⟩
      · intro later member
        have bound := lower later member
        omega
      · intro value member
        rcases List.mem_cons.mp member with equal | restMember
        · omega
        · exact Nat.le_trans monotone (lower value restMember)

/-- Every accepted intent in a mixed replay has a strictly larger ID than every
earlier intent, across restarts, resolutions, cancellation and new user turns.
The theorem projects the stored records themselves; it does not assume a trace
of distinct IDs or treat repeated completion/resolution references as intents. -/
theorem replay_intent_ids_strict (id : String) (config : Config) (task : String)
    (records : List Json) (next : Cursor app)
    (accepted : replay (init id config task app) records = .ok next) :
    (records.filterMap intentOperationId?).Pairwise (· < ·) :=
  (mixed_intents_ordered config {state := init id config task app} next records
    ⟨core_valid_init id config task, by intro prior impossible; cases impossible⟩ accepted).1

theorem replay_intent_ids_unique (id : String) (config : Config) (task : String)
    (records : List Json) (next : Cursor app)
    (accepted : replay (init id config task app) records = .ok next) :
    (records.filterMap intentOperationId?).Nodup :=
  (replay_intent_ids_strict id config task records next accepted).imp Nat.ne_of_lt

end Harness.Recovery
