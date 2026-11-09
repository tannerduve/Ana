import Harness.Core.Recovery
import Harness.Proofs.Except

/-! Frames for accepted journal records, derived from the executable parser.
These facts describe logical state changes, not filesystem durability. -/

namespace Harness.Recovery

variable {app : Application}
open Lean ExceptRules

/-- Successful intent admission is a new pending boundary and does not advance
logical state. A repeated pending action cannot admit a second intent. -/
theorem accepted_intent_frame (cursor next : (Cursor app)) (record : Json)
    (kind : record.getObjValAs? String "kind" = .ok "intent")
    (accepted : applyRecord cursor record = .ok next) :
    cursor.pending = false ∧ next.state = cursor.state ∧ next.pending = true := by
  suffices all : ExceptSuccess (fun after =>
      cursor.pending = false ∧ after.state = cursor.state ∧ after.pending = true)
      (applyRecord cursor record) from all next accepted
  simp only [applyRecord, kind, ok_bind, pure_ok, throw_error, error_bind]
  apply ExceptSuccess.bind
  intro id
  have recovery : ("intent" == "recovery") = false := by decide
  have resolution : ("intent" == "resolution") = false := by decide
  simp only [recovery, resolution, Bool.false_eq_true, if_false]
  cases node : (step cursor.state).1
  all_goals simp only [ExceptSuccess.if_iff, ExceptSuccess.bind_iff, ExceptSuccess.error_iff]
  all_goals repeat' first
    | trivial
    | (solve | simp_all only [Bool.not_eq_true])
    | (apply And.intro)
    | (intro)
    | (split)
    | (simp only [pure_ok, throw_error, error_bind, ok_bind,
        ExceptSuccess.if_iff, ExceptSuccess.bind_iff, ExceptSuccess.error_iff, ExceptSuccess.ok_iff])
  all_goals
    rename_i witnessAccepted
    split at witnessAccepted
    · cases witnessAccepted; rfl
    · obtain ⟨witness, _, witnessAccepted⟩ := ExceptSuccess.bind_ok_exists _ _ _ witnessAccepted
      cases witness with
      | none => cases witnessAccepted; rfl
      | some witness =>
        obtain ⟨_, _, witnessAccepted⟩ := ExceptSuccess.bind_ok_exists _ _ _ witnessAccepted
        cases witnessAccepted
        rfl

/-- A terminal marker changes neither the logical state nor pending status. -/
theorem accepted_terminal_frame (cursor next : (Cursor app)) (record : Json)
    (kind : record.getObjValAs? String "kind" = .ok "terminal")
    (accepted : applyRecord cursor record = .ok next) :
    next.state = cursor.state ∧ next.pending = cursor.pending := by
  suffices all : ExceptSuccess (fun after =>
      after.state = cursor.state ∧ after.pending = cursor.pending)
      (applyRecord cursor record) from all next accepted
  simp only [applyRecord, kind, ok_bind, pure_ok, throw_error, error_bind]
  apply ExceptSuccess.bind
  intro id
  have recovery : ("terminal" == "recovery") = false := by decide
  have resolution : ("terminal" == "resolution") = false := by decide
  simp only [recovery, resolution, Bool.false_eq_true, if_false]
  cases node : (step cursor.state).1
  all_goals simp only [ExceptSuccess.if_iff, ExceptSuccess.bind_iff, ExceptSuccess.error_iff, ExceptSuccess.ok_iff]
  all_goals repeat' first | trivial | (apply And.intro) | (intro)

/-- A successful completion decodes the actual stored observation against the
actual pending coalgebra action, then uses precisely that continuation. -/
theorem accepted_completion_frame (cursor next : (Cursor app)) (record : Json)
    (kind : record.getObjValAs? String "kind" = .ok "completion")
    (accepted : applyRecord cursor record = .ok next) :
    ∃ (observation : Json) (response : Reply (step cursor.state).1),
      cursor.pending = true ∧ record.getObjVal? "observation" = .ok observation ∧
      replyFromJson (step cursor.state).1 observation = .ok response ∧
      next = complete cursor response := by
  simp only [applyRecord, kind, ok_bind, pure_ok, throw_error, error_bind] at accepted
  obtain ⟨id, _, accepted⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
  have recovery : ("completion" == "recovery") = false := by decide
  have resolution : ("completion" == "resolution") = false := by decide
  have notTurn : ("completion" == "user_turn") = false := by decide
  simp only [recovery, resolution, notTurn, Bool.false_eq_true, if_false] at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · have pending : cursor.pending = true := by
          cases value : cursor.pending <;> simp_all
        obtain ⟨observation, body, accepted⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
        obtain ⟨response, decoded, final⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
        simp only [Except.ok.injEq] at final
        refine ⟨observation, response, ?_, body, decoded, final.symm⟩
        exact pending

/-- The actual record parser admits only its six documented record kinds. -/
theorem accepted_record_kind_known (cursor next : (Cursor app)) (record : Json)
    (accepted : applyRecord cursor record = .ok next) :
    ∃ kind, record.getObjValAs? String "kind" = .ok kind ∧
      kind ∈ ["intent", "completion", "terminal", "recovery", "resolution", "user_turn"] := by
  cases decoded : record.getObjValAs? String "kind" with
  | error message => simp [applyRecord, decoded] at accepted
  | ok kind =>
    refine ⟨kind, rfl, ?_⟩
    by_contra unknown
    simp only [List.mem_cons, not_or] at unknown
    obtain ⟨intent, completion, terminal, recovery, resolution, userTurn, _⟩ := unknown
    cases identifier : record.getObjValAs? Nat "id" <;>
      simp only [applyRecord, decoded, identifier, pure_ok, throw_error, ok_bind, error_bind] at accepted
    · cases accepted
    · simp only [beq_eq_false_iff_ne.mpr recovery, beq_eq_false_iff_ne.mpr resolution, beq_eq_false_iff_ne.mpr userTurn,
        Bool.false_eq_true, if_false] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted
        · simp at accepted


/-- Accepted administrative records invoke the actual typed recovery function. -/
theorem accepted_recovery_frame (cursor next : (Cursor app)) (record : Json)
    (kind : record.getObjValAs? String "kind" = .ok "recovery")
    (accepted : applyRecord cursor record = .ok next) :
    ∃ id disposition, recover cursor id disposition = .ok next := by
  simp only [applyRecord, kind, ok_bind, pure_ok, throw_error, error_bind] at accepted
  obtain ⟨id, _, accepted⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
  simp only [beq_self_eq_true, if_true] at accepted
  obtain ⟨saved, _, accepted⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
  repeat' first
    | (split at accepted)
    | (simp only [pure_ok, throw_error, ok_bind, error_bind] at accepted)
    | (cases accepted)
    | (exact ⟨id, saved.disposition, accepted⟩)

/-- app.Resolution records cannot bypass the typed resolution check in replay. -/
theorem accepted_resolution_frame (cursor next : (Cursor app)) (record : Json)
    (kind : record.getObjValAs? String "kind" = .ok "resolution")
    (accepted : applyRecord cursor record = .ok next) :
    ∃ id resolution, resolve cursor id resolution = .ok next := by
  simp only [applyRecord, kind, ok_bind, pure_ok, throw_error, error_bind] at accepted
  obtain ⟨id, _, accepted⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
  have other : ("resolution" == "recovery") = false := by decide
  simp only [other, Bool.false_eq_true, if_false, beq_self_eq_true, if_true] at accepted
  obtain ⟨resolution, _, accepted⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
  obtain ⟨source, _, accepted⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
  split at accepted
  all_goals repeat' first
    | (split at accepted)
    | (simp only [pure_ok, throw_error, ok_bind, error_bind] at accepted)
    | (cases accepted)
    | (exact ⟨id, _, accepted⟩)

end Harness.Recovery

namespace Harness.Recovery
open Lean ExceptRules
variable {app : Application}

theorem accepted_user_turn_frame (cursor next : Cursor app) (record : Json)
    (kind : record.getObjValAs? String "kind" = .ok "user_turn")
    (accepted : applyRecord cursor record = .ok next) :
    ∃ id turn task, newTurn cursor id turn task = .ok next := by
  simp only [applyRecord, kind, ok_bind, pure_ok, throw_error, error_bind] at accepted
  obtain ⟨id, _, accepted⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
  have a : ("user_turn" == "recovery") = false := by decide
  have b : ("user_turn" == "resolution") = false := by decide
  simp only [a, b, beq_self_eq_true, Bool.false_eq_true, if_false, if_true] at accepted
  obtain ⟨turn, _, accepted⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
  obtain ⟨task, _, accepted⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
  exact ⟨id, turn, task, accepted⟩

end Harness.Recovery
