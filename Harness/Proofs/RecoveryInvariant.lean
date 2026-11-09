import Harness.Proofs.Except
import Harness.Proofs.TurnFrames

/-! Shared predicate preservation through the actual journal and recovery functions.
The five RecoveryRules obligations isolate ordinary steps, grant resets, approval
queue resets, new user turns and artifact overlays. CursorProperty retains the exact suspended
uncertain continuation; no unrelated checkpoint is assumed valid. This module
adds no operational semantics or serialized witness. Durability, authenticated
provenance and physical resource settlement remain interpreter obligations. -/
namespace Harness.Recovery

variable {app : Application}
open Lean

open ExceptRules

/-- A saved tool position is tied to the exact uncertain reply that produced
the current state. This logical predicate does not replace journal grammar checks. -/
structure CursorProperty (P : (State app) → Prop) (cursor : (Cursor app)) : Prop where
  current : P cursor.state
  suspended : ∀ prior, cursor.suspended = some prior →
    P prior ∧ ∃ response : Reply (step prior).1,
      replyIsUncertain (step prior).1 response = true ∧ cursor.state = (step prior).2 response

/-- Exact frames needed to transport a state predicate through recovery. These
are local proof obligations about existing operations, not another state machine. -/
structure RecoveryRules (P : (State app) → Prop) : Prop where
  step : ∀ state, P state → ∀ response : Reply (Harness.step state).1, P ((Harness.step state).2 response)
  clearGrant : ∀ state, P state → P (advance {state with grant := none})
  approvalRetry : ∀ state, P state → ∀ call remaining, state.phase = .ask call remaining →
    P (advance {state with phase := .controlTools (call :: remaining), grant := none})
  userTurn : ∀ before after task, P before → beginTurn before task = .ok after → P after
  artifactOverlay : ∀ old current, P old → P current → ∀ call, (Harness.step old).1 = .tool call →
    P {old with artifacts := current.artifacts}

variable {P : (State app) → Prop}

/-- Checked reopening uses the valid saved tool state and the current admitted
artifact registry. A forged unrelated saved position does not satisfy the premise. -/
theorem checked_target_property (rules : RecoveryRules P) (cursor : (Cursor app)) (prior : (State app))
    (valid : CursorProperty P cursor) (accepted : checkedTarget cursor = .ok prior) :
    P prior := by
  by_cases pending : cursor.pending = true
  · by_cases invalid : (cursor.terminal || cursor.suspended.isSome) = true
    · simp [checkedTarget, pending, invalid] at accepted
    · have eq : cursor.state = prior := by simpa [checkedTarget, pending, invalid] using accepted
      exact eq ▸ valid.current
  · cases saved : cursor.suspended with
    | none => simp [checkedTarget, pending, saved] at accepted
    | some old =>
      simp only [checkedTarget, pending, Bool.false_eq_true, ↓reduceIte, saved] at accepted
      split at accepted
      · cases action : (step old).fst <;> simp only [action] at accepted
        all_goals simp at accepted
        rw [← accepted]
        exact rules.artifactOverlay old cursor.state (valid.suspended old saved).1 valid.current _ action
      · simp at accepted

theorem complete_property (rules : RecoveryRules P) (cursor : (Cursor app))
    (valid : CursorProperty P cursor) (response : Reply (step cursor.state).1) :
    CursorProperty P (complete cursor response) := by
  refine ⟨rules.step cursor.state valid.current response, ?_⟩
  intro prior saved
  simp only [complete] at saved
  split at saved
  · have equal : cursor.state = prior := Option.some.inj saved
    subst prior
    exact ⟨valid.current, response, by assumption, rfl⟩
  · contradiction

private theorem fresh_cursor_property (_config : RecoveryRules P) (state : (State app)) (valid : P state) :
    CursorProperty P {state} := by
  exact ⟨valid, by intro prior impossible; contradiction⟩

private def PropertyNode (P : (State app) → Prop) (node : (HarnessF app) (State app)) : Prop :=
  ∀ response : Reply node.1, P (node.2 response)

/-- Administrative recovery preserves the supplied predicate. Lost control,
approval and waits have explicit reset transitions; other outcomes use the actual
typed core continuation, without refunding or executing an operation. -/
theorem recover_property (rules : RecoveryRules P) (cursor next : (Cursor app)) (id : Nat)
    (disposition : Disposition) (valid : CursorProperty P cursor)
    (accepted : recover cursor id disposition = .ok next) : CursorProperty P next := by
  cases target : checkedTarget cursor with
  | error message => simp [recover, target] at accepted
  | ok prior =>
    have priorValid := checked_target_property rules cursor prior valid target
    by_cases same : id = prior.nextId
    · subst id
      cases node : step prior with
      | mk action continuation =>
        have continuationValid : ∀ response : Reply action, P (continuation response) := by
          have preserved : PropertyNode P (step prior) := rules.step prior priorValid
          rw [node] at preserved
          exact preserved
        cases action <;> cases disposition <;>
          simp only [recover, target, node, beq_self_eq_true,
            ↓reduceIte, pure_ok, throw_error, ok_bind, error_bind] at accepted
        all_goals try (cases accepted)
        all_goals first
          | exact fresh_cursor_property rules _ (rules.clearGrant prior priorValid)
          | exact fresh_cursor_property rules _ (continuationValid _)
          | repeat' first
              | (split at accepted)
              | (simp only [pure_ok, throw_error, ok_bind, error_bind, Except.map_ok, Except.map_error] at accepted)
              | (cases accepted)
              | (exact fresh_cursor_property rules _ (continuationValid _))
              | (exact fresh_cursor_property rules _
                  (rules.approvalRetry prior priorValid _ _ (by assumption)))
    · simp [recover, target, same] at accepted

/-- An accepted resolution consumes the saved operation's real continuation.
Its observation is labeled by the executable recovery function; this theorem
does not turn an operator assertion into evidence of external success. -/
theorem resolve_property (rules : RecoveryRules P) (cursor next : (Cursor app)) (id : Nat)
    (resolution : app.Resolution) (valid : CursorProperty P cursor)
    (accepted : resolve cursor id resolution = .ok next) : CursorProperty P next := by
  cases target : checkedTarget cursor with
  | error message => simp [resolve, target] at accepted
  | ok prior =>
    have priorValid := checked_target_property rules cursor prior valid target
    by_cases same : id = prior.nextId
    · subst id
      cases node : step prior with
      | mk action continuation =>
        have continuationValid : ∀ response : Reply action, P (continuation response) := by
          have preserved : PropertyNode P (step prior) := rules.step prior priorValid
          rw [node] at preserved
          exact preserved
        cases action <;>
          simp only [resolve, target, node, beq_self_eq_true, ↓reduceIte,
            pure_ok, throw_error, ok_bind, error_bind] at accepted
        all_goals try cases accepted
        case tool call =>
          repeat' first
            | (split at accepted)
            | (simp only [bind, Except.bind] at accepted)
            | (cases accepted)
            | (exact fresh_cursor_property rules _ (continuationValid _))
    · simp [resolve, target, same] at accepted

theorem new_turn_property (rules : RecoveryRules P) (cursor next : Cursor app)
    (id turn : Nat) (task : String) (valid : CursorProperty P cursor)
    (accepted : newTurn cursor id turn task = .ok next) : CursorProperty P next := by
  obtain ⟨_, _, _, _, _, _, begun, _, _, suspended, _⟩ := new_turn_contract cursor next id turn task accepted
  exact ⟨rules.userTurn cursor.state next.state task valid.current begun,
    by intro prior saved; simp [suspended] at saved⟩

private theorem property_cursor_frame (_config : RecoveryRules P) (cursor : (Cursor app)) (valid : CursorProperty P cursor)
    (pending terminal : Bool) (witness : Option app.Witness) :
    CursorProperty P {cursor with pending, terminal, editWitness := witness} := ⟨valid.current, valid.suspended⟩

/-- Every accepted journal record preserves the supplied predicate, including
administrative recovery and resolution records. This is about validated JSON,
not durable ordering, authenticated provenance or the truth of operator assertions. -/
theorem apply_record_property (rules : RecoveryRules P) (cursor next : (Cursor app)) (record : Json)
    (valid : CursorProperty P cursor) (accepted : applyRecord cursor record = .ok next) :
    CursorProperty P next := by
  suffices all : ExceptSuccess (CursorProperty P) (applyRecord cursor record) from all next accepted
  simp only [applyRecord]
  apply ExceptSuccess.bind
  intro kind
  apply ExceptSuccess.bind
  intro id
  simp only [pure_ok, throw_error, error_bind, ok_bind, ExceptSuccess.if_iff, ExceptSuccess.bind_iff, ExceptSuccess.error_iff]
  repeat' first
    | trivial
    | exact valid
    | exact property_cursor_frame rules cursor valid _ _ _
    | exact complete_property rules cursor valid _
    | exact fun result accepted => recover_property rules cursor result id _ valid accepted
    | exact fun result accepted => resolve_property rules cursor result id _ valid accepted
    | exact fun result accepted => new_turn_property rules cursor result id _ _ valid accepted
    | (apply And.intro)
    | (split)
    | (simp only [ExceptSuccess.if_iff, ExceptSuccess.bind_iff, ExceptSuccess.error_iff, ExceptSuccess.ok_iff])
    | (intro)

/-- Starting with a valid initial state, accepted records preserve the predicate
through ordinary completions and explicit administrative recovery/resolution. -/
theorem replay_property (rules : RecoveryRules P) (initial : (State app)) (valid : P initial)
    (records : List Json) (next : (Cursor app))
    (accepted : replay initial records = .ok next) : CursorProperty P next := by
  exact ExceptSuccess.foldlM_preserves (CursorProperty P) applyRecord records
    {state := initial} next (fresh_cursor_property rules initial valid)
    (fun record _ cursor next valid accepted =>
      apply_record_property rules cursor next record valid accepted) accepted

end Harness.Recovery
