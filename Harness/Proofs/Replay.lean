import Harness.Proofs.RecordFrames
import Harness.Proofs.Except
import Harness.Proofs.Recovery
import Harness.Proofs.Trace

namespace Harness.Recovery

variable {app : Application}
open Lean

open ExceptRules

/-- Accepted completion decoding is the only premise concerning the serialization
codec. No injectivity or roundtrip property of opaque JSON compression is assumed. -/
theorem completion_record_follows_step (cursor : (Cursor app)) (record observation : Json)
    (response : Reply (step cursor.state).1)
    (kind : record.getObjValAs? String "kind" = .ok "completion")
    (id : record.getObjValAs? Nat "id" = .ok cursor.state.nextId)
    (body : record.getObjVal? "observation" = .ok observation)
    (decoded : replyFromJson (step cursor.state).1 observation = .ok response)
    (pending : cursor.pending = true) (terminal : cursor.terminal = false) :
    applyRecord cursor record = .ok (complete cursor response) := by
  simp [applyRecord, kind, id, body, decoded, pending, terminal]

theorem completed_state_is_continuation (cursor : (Cursor app))
    (response : Reply (step cursor.state).1) :
    (complete cursor response).state = (step cursor.state).2 response := rfl

/-- Suspended state is the same pre-operation state, not a separately supplied
checkpoint. It exists exactly for uncertain/interrupted tool completions. -/
theorem completed_suspended_source (cursor : (Cursor app))
    (response : Reply (step cursor.state).1) :
    (complete cursor response).suspended =
      if replyIsUncertain (step cursor.state).1 response then some cursor.state else none := rfl

theorem completed_preserves_config (cursor : (Cursor app))
    (response : Reply (step cursor.state).1) :
    (complete cursor response).state.config = cursor.state.config :=
  config_preserved cursor.state response

theorem completed_preserves_budgets (cursor : (Cursor app))
    (response : Reply (step cursor.state).1) (valid : BudgetValid cursor.state) :
    BudgetValid (complete cursor response).state :=
  budget_preserved cursor.state valid response

/-- This is a sequence of successfully decoded observations, including the exact
saved suspended position after a final uncertain reply. Intent framing and codec
admission are covered by `completion_record_follows_step`; no IO is executed here. -/
inductive CompletedPrefix : (Cursor app) → List (ObservedStep app) → (Cursor app) → Prop where
  | nil (cursor : (Cursor app)) : CompletedPrefix cursor [] cursor
  | cons (cursor : (Cursor app)) (response : Reply (step cursor.state).1)
      {events : List (ObservedStep app)} {last : (Cursor app)}
      (tail : CompletedPrefix (complete cursor response) events last) :
      CompletedPrefix cursor (observe cursor.state response :: events) last

/-- Completed observation replay reconstructs the actual execution state, not
merely a uniquely determined result of the replay function. -/
theorem completed_prefix_corresponds {first last : (Cursor app)} {events : List (ObservedStep app)}
    (records : CompletedPrefix first events last) :
    ExecutionTrace first.state events last.state := by
  induction records with
  | nil => exact .nil _
  | cons cursor response tail ih =>
    exact .cons (c := step) (observe := observe) cursor.state response ih

theorem completed_prefix_reachable {id : String} {config : Config} {task : String}
    {last : (Cursor app)} {events : List (ObservedStep app)}
    (records : CompletedPrefix {state := init id config task app} events last) :
    Reachable id config task last.state :=
  (completed_prefix_corresponds records).reachable .initial

/-- A terminal record adds only the durable terminal marker. -/
theorem terminal_record_preserves_state (cursor next : (Cursor app)) (record : Json)
    (kind : record.getObjValAs? String "kind" = .ok "terminal")
    (accepted : applyRecord cursor record = .ok next) : next.state = cursor.state := by
  exact (accepted_terminal_frame cursor next record kind accepted).1

/-- Administrative records are handled separately: an ordinary prefix consists
only of intent, completion and terminal records. This predicate says nothing
about their validity; validity is the successful result of the actual replay. -/
def OrdinaryRecord (record : Json) : Prop :=
  record.getObjValAs? String "kind" = .ok "intent" ∨
  record.getObjValAs? String "kind" = .ok "completion" ∨
  record.getObjValAs? String "kind" = .ok "terminal"

private theorem ordinary_record_trace (cursor : (Cursor app)) (record : Json)
    (ordinary : OrdinaryRecord record) :
    ExceptSuccess (fun next => ∃ events, ExecutionTrace cursor.state events next.state)
      (applyRecord cursor record) := by
  intro next accepted
  rcases ordinary with kind | kind | kind
  · have unchanged := (accepted_intent_frame cursor next record kind accepted).2.1
    refine ⟨[], ?_⟩
    rw [unchanged]
    exact .nil _
  · obtain ⟨observation, response, _, _, _, equal⟩ := accepted_completion_frame cursor next record kind accepted
    subst next
    exact ⟨[_], .cons (c := step) (observe := observe) cursor.state response (.nil _)⟩
  · have unchanged := (accepted_terminal_frame cursor next record kind accepted).1
    refine ⟨[], ?_⟩
    rw [unchanged]
    exact .nil _

/-- Every successfully accepted ordinary JSON prefix follows the executable
coalgebra, including intents with no completion. No encoder injectivity,
codec-roundtrip, checksum, durability or external-effect assumption is used. -/
theorem ordinary_prefix_corresponds (first last : (Cursor app)) (records : List Json)
    (ordinary : ∀ record ∈ records, OrdinaryRecord record)
    (accepted : records.foldlM applyRecord first = .ok last) :
    ∃ events, ExecutionTrace first.state events last.state := by
  apply ExceptSuccess.foldlM_preserves
    (fun cursor : (Cursor app) => ∃ events, ExecutionTrace first.state events cursor.state)
    applyRecord records first last ⟨[], .nil _⟩ ?_ accepted
  intro record member before after previous decoded
  obtain ⟨earlier, earlierTrace⟩ := previous
  obtain ⟨later, laterTrace⟩ := ordinary_record_trace before record (ordinary record member) after decoded
  exact ⟨earlier ++ later, earlierTrace.append laterTrace⟩

theorem ordinary_replay_reachable (id : String) (config : Config) (task : String)
    (records : List Json) (last : (Cursor app))
    (ordinary : ∀ record ∈ records, OrdinaryRecord record)
    (accepted : replay (init id config task app) records = .ok last) :
    Reachable id config task last.state := by
  obtain ⟨events, trace⟩ := ordinary_prefix_corresponds {state := init id config task app} last records ordinary accepted
  exact trace.reachable .initial

/-- The typed fields of a recorded intent. The serialized action comparison is
the runner's actual wire comparison, not an assumed injective JSON encoding. -/
structure IntentFields (state : (State app)) (record : Json) (witness : Option app.Witness) : Prop where
  kind : record.getObjValAs? String "kind" = .ok "intent"
  id : record.getObjValAs? Nat "id" = .ok state.nextId
  action : ∃ value, record.getObjVal? "action" = .ok value ∧
    value.compress = (actionToJson (step state).1).compress
  witnessDecoded : (match record.getObjVal? "editWitness" with
    | .error _ => .ok none
    | .ok value => fromJson? value) = (Except.ok witness : Except String (Option app.Witness))
  witnessValid : ∀ value, witness = some value → validateWitness (step state).1 value = .ok ()

theorem intent_record_follows (cursor : (Cursor app)) (record : Json) (witness : Option app.Witness)
    (fields : IntentFields cursor.state record witness)
    (pending : cursor.pending = false) (terminal : cursor.terminal = false)
    (nonterminal : ∀ outcome, (step cursor.state).1 ≠ .finish outcome) :
    applyRecord cursor record = .ok {cursor with pending := true, editWitness := witness} := by
  obtain ⟨action, encoded, sameWire⟩ := fields.action
  have noRecovery : ("intent" == "recovery") = false := by decide
  have noResolution : ("intent" == "resolution") = false := by decide
  have noTurn : ("intent" == "user_turn") = false := by decide
  simp only [applyRecord, fields.kind, fields.id, ok_bind, noRecovery, noResolution, noTurn,
    Bool.false_eq_true, if_false, terminal, pending, bne_self_eq_false, encoded, sameWire]
  cases selected : (step cursor.state).1
  all_goals try {exact (nonterminal _ selected).elim}
  all_goals
    have decoded := fields.witnessDecoded
    cases field : record.getObjVal? "editWitness" with
    | error message =>
      simp only [field, Except.ok.injEq] at decoded
      cases decoded
      simp
    | ok value =>
      simp only [field] at decoded
      simp only [decoded, ok_bind]
      cases witness with
      | none => rfl
      | some witness =>
        have valid := fields.witnessValid witness rfl
        simp only [selected] at valid
        simp [valid]

/-- One live ordinary execution together with the recorded intent/completion
fields. Each completion is the exact encoded reply of that live step; its codec
roundtrip is explicit. Valid edit witnesses are allowed. No runtime or storage
properties are hidden in this relation. -/
inductive RecordedExecution : (State app) → List Json → (State app) → Prop where
  | nil (state : (State app)) : RecordedExecution state [] state
  | cons (state : (State app)) (response : Reply (step state).1) (intent completion : Json)
      (witness : Option app.Witness)
      (intentFields : IntentFields state intent witness)
      (completionKind : completion.getObjValAs? String "kind" = .ok "completion")
      (completionId : completion.getObjValAs? Nat "id" = .ok state.nextId)
      (completionBody : completion.getObjVal? "observation" = .ok (replyToJson (step state).1 response))
      (roundtrip : replyFromJson (step state).1 (replyToJson (step state).1 response) = .ok response)
      {records : List Json} {last : (State app)}
      (tail : RecordedExecution ((step state).2 response) records last) :
      RecordedExecution state (intent :: completion :: records) last

private theorem reply_not_finish (action : (Action app)) (response : Reply action) :
    ∀ outcome, action ≠ .finish outcome := by
  intro outcome equal
  cases equal
  exact response.elim

/-- Recorded live replies reconstruct that exact logical state. The premise is
a live-step trace plus per-record field/codec contracts, never successful replay
or equality of the desired final state. Pending and terminal flags are settled
after every completed pair; uncertain outcomes retain their suspended source via
`completed_suspended_source`. -/
theorem recorded_execution_replays {first last : (State app)} {records : List Json}
    (recorded : RecordedExecution first records last) (cursor : (Cursor app))
    (state : cursor.state = first) (pending : cursor.pending = false) (terminal : cursor.terminal = false) :
    ∃ result, records.foldlM applyRecord cursor = .ok result ∧ result.state = last ∧
      result.pending = false ∧ result.terminal = false := by
  induction recorded generalizing cursor with
  | nil first => exact ⟨cursor, rfl, state, pending, terminal⟩
  | cons first response intent completion witness intentFields kind id body roundtrip tail ih =>
    subst first
    let waiting : (Cursor app) := {cursor with pending := true, editWitness := witness}
    have intentDone : applyRecord cursor intent = .ok waiting :=
      intent_record_follows cursor intent witness intentFields pending terminal
        (reply_not_finish _ response)
    have completionDone : applyRecord waiting completion = .ok (complete waiting response) :=
      completion_record_follows_step waiting completion _ response kind id body roundtrip rfl terminal
    obtain ⟨result, remaining, final, noPending, noTerminal⟩ := ih (complete waiting response) rfl rfl rfl
    refine ⟨result, ?_, final, noPending, noTerminal⟩
    simpa only [List.foldlM_cons, intentDone, completionDone, ok_bind] using remaining

end Harness.Recovery
