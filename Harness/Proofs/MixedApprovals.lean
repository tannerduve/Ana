import Harness.Proofs.Approvals
import Harness.Proofs.Administrative
import Harness.Proofs.RecoveryLedger
import Harness.Proofs.RecordFrames

/-! Approval provenance across ordinary completions and administrative recovery.
The boundary is a newly accepted tool intent; restoring a pending action is not
a second dispatch. Typed approval observations are trusted inputs. -/

open Lean
namespace Harness.Recovery

variable {app : Application}
open ExceptRules
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

/-- A grant remains unused only before a tool intent has been accepted. The
persisted state itself keeps the grant while that one operation is pending. -/
def ReadyGrant (cursor : (Cursor app)) (call : (Call app)) : Prop :=
  cursor.state.grant = some call ∧
    (cursor.pending = true → ∀ tool remaining, cursor.state.phase ≠ .tool tool remaining)

/-- An actual completion record decodes to the trusted typed approval reply.
No model text or administrative assertion is interpreted as this evidence. -/
def ApprovalRecord (cursor : (Cursor app)) (record : Json) (call : (Call app)) : Prop :=
  (record.getObjValAs? String "kind") = .ok "completion" ∧ cursor.pending = true ∧
    ∃ observation response,
      record.getObjVal? "observation" = .ok observation ∧
      replyFromJson (step cursor.state).1 observation = .ok response ∧
      approvedCall (step cursor.state).1 response = some call

/-- The source record is a reply to an ask for this exact call, and its decoded
response is the typed approval constructor. Journal authenticity is external. -/
theorem ApprovalRecord.trusted {cursor : (Cursor app)} {record : Json} {call : (Call app)}
    (source : ApprovalRecord cursor record call) :
    ∃ observation response,
      record.getObjVal? "observation" = .ok observation ∧
      replyFromJson (step cursor.state).1 observation = .ok response ∧
      (step cursor.state).1 = .ask call ∧ HEq response ApprovalObservation.approved := by
  obtain ⟨_, _, observation, response, observed, decoded, approved⟩ := source
  obtain ⟨asked, trusted⟩ := approvedCall_trusted approved
  exact ⟨observation, response, observed, decoded, asked, trusted⟩

private theorem model_not_tool (state : (State app)) (request : ModelRequest)
    (model : (step state).1 = .model request) :
    ∀ call remaining, state.phase ≠ .tool call remaining := by
  intro call remaining phase
  simp only [step, phase] at model
  by_cases guard : (authorized state.config state.grant call && artifactAuthorized state call && decide (0 < state.toolDispatches) && decide (state.toolDispatches ≤ state.config.maxToolCalls)) = true
  · simp [guard] at model
  · simp [guard] at model

private theorem checked_target_model (cursor : (Cursor app)) (prior : (State app)) (request : ModelRequest)
    (target : checkedTarget cursor = .ok prior) (model : (step prior).1 = .model request) :
    cursor.pending = true ∧ prior = cursor.state := by
  by_cases pending : cursor.pending = true
  · refine ⟨pending, ?_⟩
    by_cases invalid : (cursor.terminal || cursor.suspended.isSome) = true
    · simp [checkedTarget, pending, invalid] at target
    · simpa [checkedTarget, pending, invalid] using target.symm
  · cases saved : cursor.suspended with
    | none => simp [checkedTarget, pending, saved] at target
    | some old =>
      simp only [checkedTarget, pending, Bool.false_eq_true, ↓reduceIte, saved] at target
      split at target
      · cases emitted : (step old).1 <;> simp only [emitted] at target
        all_goals try contradiction
        case tool call =>
          simp only [pure_ok, Except.ok.injEq] at target
          obtain ⟨remaining, phase⟩ := emitted_tool_phase old call emitted
          have phase' : prior.phase = .tool call remaining := by rw [← target]; exact phase
          exact (model_not_tool prior request model call remaining phase').elim
      · contradiction

private theorem resolve_clears_grant (cursor next : (Cursor app)) (id : Nat) (resolution : app.Resolution)
    (accepted : resolve cursor id resolution = .ok next) : next.state.grant = none := by
  cases target : checkedTarget cursor with
  | error message => simp [resolve, target] at accepted
  | ok prior =>
    obtain ⟨response, result, _, call, emitted⟩ := resolve_continuation cursor next prior id resolution target accepted
    subst next
    exact emitted_tool_reply_clears_grant prior response call emitted

private def GrantNode (state : (State app)) (node : (HarnessF app) (State app)) : Prop :=
  ∀ response : Reply node.1, ∀ call, (node.2 response).grant = some call →
    state.grant = some call ∨ approvedCall node.1 response = some call

private theorem recover_grant_source (cursor next : (Cursor app)) (id : Nat) (disposition : Disposition)
    (accepted : recover cursor id disposition = .ok next) (call : (Call app))
    (grant : next.state.grant = some call) : ReadyGrant cursor call := by
  cases target : checkedTarget cursor with
  | error message => simp [recover, target] at accepted
  | ok prior =>
    by_cases same : id = prior.nextId
    · subst id
      cases node : step prior with
      | mk action continuation =>
        have source : ∀ response : Reply action, ∀ proposed,
            (continuation response).grant = some proposed →
            prior.grant = some proposed ∨ approvedCall action response = some proposed := by
          have source : GrantNode prior (step prior) := grant_step_source prior
          rw [node] at source
          exact source
        cases action with
        | tool proposed =>
          obtain ⟨response, result, _⟩ := recover_tool_continuation cursor next prior prior.nextId disposition proposed target (by simp [node]) accepted
          have cleared := emitted_tool_reply_clears_grant prior response proposed (by simp [node])
          simp [result, cleared] at grant
        | model request =>
          cases disposition <;>
            simp only [recover, target, node, ok_bind, beq_self_eq_true, ↓reduceIte,
              pure_ok, throw_error, error_bind] at accepted
          all_goals try contradiction
          case modelLost =>
            cases accepted
            obtain ⟨pending, equal⟩ := checked_target_model cursor prior request target (by simp [node])
            obtain inherited | impossible := source _ call grant
            · refine ⟨by simpa [equal] using inherited, ?_⟩
              intro _ tool remaining phase
              exact model_not_tool prior request (by simp [node]) tool remaining (by simpa [equal] using phase)
            · simp [approvedCall] at impossible
        | control =>
          cases disposition <;> simp [recover, target, node] at accepted
          cases accepted
          simp [advance] at grant
        | wait delay =>
          cases disposition <;> simp [recover, target, node] at accepted
          cases accepted
          simp [advance] at grant
        | finish outcome =>
          cases disposition <;> simp [recover, target, node] at accepted
        | ask proposed =>
          cases disposition <;> simp [recover, target, node] at accepted
          cases phase : prior.phase <;> simp [phase] at accepted
          cases accepted
          simp [advance] at grant
    · simp [recover, target, same] at accepted

private def PhaseGrantNode (state : (State app)) (node : (HarnessF app) (State app)) : Prop :=
  ∀ (response : Reply node.1) (call : (Call app)), (node.2 response).grant = some call →
    ∀ proposed remaining, state.phase ≠ .tool proposed remaining

private theorem reply_grant_excludes_tool_phase (state : (State app)) :
    ∀ (response : Reply (step state).1) (call : (Call app)),
    ((step state).2 response).grant = some call →
    ∀ proposed remaining, state.phase ≠ .tool proposed remaining := by
  change PhaseGrantNode state (step state)
  cases phase : state.phase
  all_goals try (solve | simp [PhaseGrantNode, phase])
  case tool proposed remaining =>
    simp only [step, phase]
    by_cases guard : (authorized state.config state.grant proposed && artifactAuthorized state proposed && decide (0 < state.toolDispatches) && decide (state.toolDispatches ≤ state.config.maxToolCalls)) = true
    · erw [if_pos guard]
      intro response call grant
      simp [advance, tool_reply_clears_grant] at grant
    · erw [if_neg guard]
      intro response
      exact response.elim

private theorem complete_grant_source (cursor : (Cursor app)) (response : Reply (step cursor.state).1)
    (call : (Call app)) (grant : (complete cursor response).state.grant = some call) :
    ReadyGrant cursor call ∨ approvedCall (step cursor.state).1 response = some call := by
  obtain inherited | approved := grant_step_source cursor.state response call grant
  · exact Or.inl ⟨inherited, fun _ => reply_grant_excludes_tool_phase cursor.state response call grant⟩
  · exact Or.inr approved


private theorem new_intent_not_tool (cursor next : (Cursor app)) (record : Json) (call : (Call app))
    (kind : record.getObjValAs? String "kind" = .ok "intent")
    (accepted : applyRecord cursor record = .ok next) (ready : ReadyGrant next call) :
    ∀ proposed, (step cursor.state).1 ≠ .tool proposed := by
  obtain ⟨_, state, pending⟩ := accepted_intent_frame cursor next record kind accepted
  intro proposed emitted
  obtain ⟨remaining, phase⟩ := emitted_tool_phase cursor.state proposed emitted
  exact ready.2 pending proposed remaining (by simpa [state] using phase)

private theorem recovery_record_source (cursor next : (Cursor app)) (record : Json) (call : (Call app))
    (kind : record.getObjValAs? String "kind" = .ok "recovery")
    (accepted : applyRecord cursor record = .ok next) (ready : ReadyGrant next call) :
    ReadyGrant cursor call := by
  suffices all : ExceptSuccess (fun next => ReadyGrant next call → ReadyGrant cursor call)
      (applyRecord cursor record) from all next accepted ready
  simp only [applyRecord, kind, ok_bind, beq_self_eq_true, ↓reduceIte,
    pure_ok, throw_error, error_bind]
  apply ExceptSuccess.bind
  intro id
  apply ExceptSuccess.bind
  intro saved
  rw [ExceptSuccess.if_iff]
  constructor
  · intro _ next accepted ready
    exact recover_grant_source cursor next id saved.disposition accepted call ready.1
  · intro _
    simp only [ExceptSuccess.error_iff]

private theorem resolution_record_clears (cursor next : (Cursor app)) (record : Json)
    (kind : record.getObjValAs? String "kind" = .ok "resolution")
    (accepted : applyRecord cursor record = .ok next) : next.state.grant = none := by
  suffices all : ExceptSuccess (fun next => next.state.grant = none)
      (applyRecord cursor record) from all next accepted
  simp only [applyRecord, kind, ok_bind, beq_self_eq_true, ↓reduceIte,
    pure_ok, throw_error, error_bind]
  apply ExceptSuccess.bind
  intro id
  have different : ("resolution" == "recovery") = false := by decide
  simp only [different, Bool.false_eq_true, ↓reduceIte]
  apply ExceptSuccess.bind
  intro resolution
  apply ExceptSuccess.bind
  intro source
  split <;> simp only [ExceptSuccess.if_iff, ExceptSuccess.error_iff]
  all_goals constructor
  all_goals first
    | (exact fun _ next accepted => resolve_clears_grant cursor next id _ accepted)
    | (exact fun _ => trivial)


private theorem apply_record_grant_source (cursor next : (Cursor app)) (record : Json) (call : (Call app))
    (accepted : applyRecord cursor record = .ok next) (ready : ReadyGrant next call) :
    ReadyGrant cursor call ∨ ApprovalRecord cursor record call := by
  obtain ⟨kind, decoded, known⟩ := accepted_record_kind_known cursor next record accepted
  simp only [List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with intent | completion | terminal | recovery | resolution | userTurn
  · subst kind
    obtain ⟨pending, state, _⟩ := accepted_intent_frame cursor next record decoded accepted
    exact Or.inl ⟨by simpa [state] using ready.1, by simp [pending]⟩
  · subst kind
    obtain ⟨observation, response, pending, observed, parsed, equal⟩ :=
      accepted_completion_frame cursor next record decoded accepted
    have grant : (complete cursor response).state.grant = some call := by
      simpa [equal] using ready.1
    obtain inherited | approved := complete_grant_source cursor response call grant
    · exact Or.inl inherited
    · exact Or.inr ⟨decoded, pending, observation, response, observed, parsed, approved⟩
  · subst kind
    obtain ⟨state, pending⟩ := accepted_terminal_frame cursor next record decoded accepted
    exact Or.inl ⟨by simpa [state] using ready.1, by simpa [state, pending] using ready.2⟩
  · subst kind
    exact Or.inl (recovery_record_source cursor next record call decoded accepted ready)
  · subst kind
    have cleared := resolution_record_clears cursor next record decoded accepted
    have grant := ready.1
    simp [cleared] at grant
  · subst kind
    obtain ⟨id, turn, task, started⟩ := accepted_user_turn_frame cursor next record decoded accepted
    obtain ⟨_, _, _, _, _, _, begun, _⟩ := new_turn_contract cursor next id turn task started
    have grant := ready.1
    rw [(begin_turn_contract cursor.state next.state task begun).1] at grant
    simp [turnCandidate] at grant

/-- Every intermediate boundary retains the same unused grant. The edge clause
also excludes accepted tool intents, including ones whose completion was lost. -/
inductive GrantContinuity (call : (Call app)) : (Cursor app) → List Json → (Cursor app) → Prop where
  | nil (cursor : (Cursor app)) (ready : ReadyGrant cursor call) : GrantContinuity call cursor [] cursor
  | cons {first middle last : (Cursor app)} {record : Json} {rest : List Json}
      (ready : ReadyGrant first call) (accepted : applyRecord first record = .ok middle)
      (unused : record.getObjValAs? String "kind" = .ok "intent" →
        ∀ proposed, (step first.state).1 ≠ .tool proposed)
      (tail : GrantContinuity call middle rest last) :
      GrantContinuity call first (record :: rest) last

theorem GrantContinuity.first_ready {call : (Call app)} {first last : (Cursor app)} {records : List Json}
    (continuity : GrantContinuity call first records last) : ReadyGrant first call := by
  cases continuity with
  | nil _ ready => exact ready
  | cons ready _ _ _ => exact ready

/-- The approval is an actual typed completion in this record sequence; the
following sequence continuously retains its unused exact-call grant. -/
def ApprovalOrigin (first last : (Cursor app)) (records : List Json) (call : (Call app)) : Prop :=
  ∃ beforeRecords record suffix before after,
    records = beforeRecords ++ record :: suffix ∧
    beforeRecords.foldlM applyRecord first = .ok before ∧
    applyRecord before record = .ok after ∧ ApprovalRecord before record call ∧
    GrantContinuity call after suffix last

/-- Source and continuity are derived together through real accepted records,
including administrative recovery and resolution. -/
theorem mixed_grant_source (first last : (Cursor app)) (records : List Json) (call : (Call app))
    (accepted : records.foldlM applyRecord first = .ok last) (ready : ReadyGrant last call) :
    GrantContinuity call first records last ∨ ApprovalOrigin first last records call := by
  induction records generalizing first with
  | nil =>
    simp only [List.foldlM_nil, pure_ok, Except.ok.injEq] at accepted
    subst last
    exact Or.inl (.nil first ready)
  | cons record rest ih =>
    simp only [List.foldlM_cons] at accepted
    obtain ⟨middle, head, tail⟩ := ExceptSuccess.bind_ok_exists _ _ _ accepted
    obtain continuity | origin := ih middle tail
    · have middleReady := continuity.first_ready
      obtain previous | approved := apply_record_grant_source first middle record call head middleReady
      · exact Or.inl (.cons previous head (fun kind => new_intent_not_tool first middle record call kind head middleReady) continuity)
      · exact Or.inr ⟨[], record, rest, first, middle, rfl, rfl, head, approved, continuity⟩
    · obtain ⟨beforeRecords, approvedRecord, suffix, before, after, equality, prefixAccepted, approvedAccepted, approval, continuity⟩ := origin
      refine Or.inr ⟨record :: beforeRecords, approvedRecord, suffix, before, after, ?_, ?_, approvedAccepted, approval, continuity⟩
      · simp [equality]
      · simpa only [List.foldlM_cons, head, ok_bind] using prefixAccepted

/-- At a NEW accepted tool-intent boundary, an ask-policy tool has an earlier
trusted approval for its full exact call under the frozen configuration. The
intervening accepted records neither consume nor invalidate that grant. Merely
re-exposing a pending action is not a new intent and is not a redispatch theorem.
Authenticity of recorded observations and intent-before-physical-dispatch remain
runner/journal obligations. No claim about the truth of operator assertions is made. -/
theorem new_ask_intent_has_continuous_approval (id : String) (config : Config) (task : String)
    (records : List Json) (cursor next : (Cursor app)) (record : Json) (call : (Call app))
    (replayed : replay (init id config task app) records = .ok cursor)
    (kind : record.getObjValAs? String "kind" = .ok "intent")
    (accepted : applyRecord cursor record = .ok next)
    (emitted : (step cursor.state).1 = .tool call) (asked : policy config call = .ask) :
    ∃ beforeRecords approvalRecord suffix before after,
      records = beforeRecords ++ approvalRecord :: suffix ∧
      replay (init id config task app) beforeRecords = .ok before ∧
      applyRecord before approvalRecord = .ok after ∧ ApprovalRecord before approvalRecord call ∧
      before.state.config = config ∧ cursor.state.config = config ∧
      GrantContinuity call after suffix cursor := by
  have frozen := (replay_core_valid id config task records cursor replayed).current.frozen
  have grant := emitted_ask_tool_requires_exact_grant cursor.state call emitted (by simpa [frozen] using asked)
  obtain ⟨pending, _, _⟩ := accepted_intent_frame cursor next record kind accepted
  have ready : ReadyGrant cursor call := ⟨grant, by simp [pending]⟩
  obtain continuity | origin := mixed_grant_source {state := init id config task app} cursor records call replayed ready
  · have initial := continuity.first_ready.1
    simp [init] at initial
  · obtain ⟨beforeRecords, approvalRecord, suffix, before, after, equality, prefixAccepted, approvalAccepted, approved, continuity⟩ := origin
    exact ⟨beforeRecords, approvalRecord, suffix, before, after, equality, prefixAccepted,
      approvalAccepted, approved, (replay_core_valid id config task beforeRecords before prefixAccepted).current.frozen,
      frozen, continuity⟩

/-- Once a tool intent has been accepted, any later new ask-policy tool intent
requires a newly decoded approval in the intervening records. This covers lost
completions and administrative settlement as well as ordinary tool replies. -/
theorem next_intent_needs_fresh_approval (first afterFirst cursor afterNext : (Cursor app))
    (firstRecord nextRecord : Json) (records : List Json) (firstCall nextCall : (Call app))
    (firstKind : firstRecord.getObjValAs? String "kind" = .ok "intent")
    (firstAccepted : applyRecord first firstRecord = .ok afterFirst)
    (firstEmitted : (step first.state).1 = .tool firstCall)
    (between : records.foldlM applyRecord afterFirst = .ok cursor)
    (nextKind : nextRecord.getObjValAs? String "kind" = .ok "intent")
    (nextAccepted : applyRecord cursor nextRecord = .ok afterNext)
    (nextEmitted : (step cursor.state).1 = .tool nextCall)
    (asked : policy cursor.state.config nextCall = .ask) :
    ApprovalOrigin afterFirst cursor records nextCall := by
  obtain ⟨_, firstState, firstPending⟩ := accepted_intent_frame first afterFirst firstRecord firstKind firstAccepted
  obtain ⟨remaining, firstPhase⟩ := emitted_tool_phase first.state firstCall firstEmitted
  have consumed : ¬ ReadyGrant afterFirst nextCall := by
    intro ready
    exact ready.2 firstPending firstCall remaining (by simpa [firstState] using firstPhase)
  obtain ⟨nextPending, _, _⟩ := accepted_intent_frame cursor afterNext nextRecord nextKind nextAccepted
  have ready : ReadyGrant cursor nextCall := ⟨emitted_ask_tool_requires_exact_grant cursor.state nextCall nextEmitted asked,
    by simp [nextPending]⟩
  obtain old | fresh := mixed_grant_source afterFirst cursor records nextCall between ready
  · exact (consumed old.first_ready).elim
  · exact fresh

end Harness.Recovery
