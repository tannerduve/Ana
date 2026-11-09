import Harness.Proofs.Except
import Harness.Proofs.History
import Harness.Proofs.Compaction
import Harness.Proofs.ToolReplies

namespace Harness

variable {app : Application}
open Lean

open ExceptRules

/-- Independent extraction from retained raw content; it does not consult phase,
normalized calls, seen IDs or the dispatch log. -/
def resultId? (block : Json) : Option String :=
  if (contentString block "type").toOption = some "tool_result" then
    (contentString block "tool_use_id").toOption
  else none

def retainedResultIds (history : List Message) : List String :=
  history.flatMap fun message => message.content.toList.filterMap resultId?

private theorem accepted_block_has_no_result (acc out : List RawCall × String) (block : Json)
    (accepted : parseContentBlock acc block = .ok out) : resultId? block = none := by
  cases kind : contentString block "type" with
  | error message => simp [parseContentBlock, kind] at accepted
  | ok value =>
    by_cases result : value = "tool_result"
    · subst value
      simp [parseContentBlock, kind] at accepted
    · simp [resultId?, kind, result, Except.toOption]

private theorem accepted_blocks_have_no_result (blocks : List Json) (acc out : List RawCall × String)
    (accepted : blocks.foldlM parseContentBlock acc = .ok out) :
    blocks.filterMap resultId? = [] := by
  induction blocks generalizing acc with
  | nil => rfl
  | cons block rest ih =>
    simp only [List.foldlM_cons] at accepted
    cases parsed : parseContentBlock acc block with
    | error message => simp [parsed] at accepted
    | ok next =>
      simp only [parsed, ok_bind] at accepted
      simp [accepted_block_has_no_result acc next block parsed, ih next accepted]

/-- Model-supplied assistant content cannot smuggle a tool-result record into
authoritative history, even if its normalized call list looks valid. -/
theorem accepted_assistant_has_no_results (response : ModelResponse)
    (valid : validateModelResponse response = .ok ()) :
    response.content.toList.filterMap resultId? = [] := by
  obtain ⟨decoded, accepted, _, _⟩ := validateModelResponse_sound response valid
  exact accepted_blocks_have_no_result _ _ _ accepted

theorem resultId_generated (call : (Call app)) (text : String) (isError : Bool) :
    resultId? (Json.mkObj [("type", toJson "tool_result"), ("tool_use_id", toJson call.id),
      ("content", toJson text), ("is_error", toJson isError)]) = some call.id := by
  rfl

@[simp] theorem resultId_text (text : String) : resultId? (textBlock text) = none := by
  rfl

theorem appendResult_retained_ids (state : (State app)) (call : (Call app)) (text : String) (isError : Bool) :
    retainedResultIds (appendResult state call text isError).history =
      retainedResultIds state.history ++ [call.id] := by
  have history : state.history = state.history.reverse.reverse := by simp
  cases reversed : state.history.reverse with
  | nil =>
    have empty : state.history = [] := by simpa [reversed] using history
    simp [appendResult, empty, retainedResultIds, resultId_generated]
  | cons last rest =>
    have original : state.history = rest.reverse ++ [last] := by simpa [reversed] using history
    simp only [appendResult, reversed]
    split <;> simp [retainedResultIds, List.reverse_cons, original, resultId_generated,
      List.flatMap_append, List.filterMap_append, List.append_assoc]

private theorem assistant_retained_ids (state : (State app)) (response : ModelResponse)
    (accepted : validateModelResponse response = .ok ()) :
    retainedResultIds (state.history ++ [{role := "assistant", content := response.content}]) =
      retainedResultIds state.history := by
  simp [retainedResultIds, List.flatMap_append, accepted_assistant_has_no_results response accepted]

def ResultsValid (state : (State app)) : Prop :=
  (retainedResultIds state.history).Nodup ∧
    ∀ id ∈ retainedResultIds state.history, RetiredCall id state

/-- A raw-history update either retains exactly the old result IDs, or appends
one result for a call in the admitted current queue and retires that identity. -/
def ResultUpdate (before after : (State app)) : Prop :=
  retainedResultIds after.history = retainedResultIds before.history ∨
    ∃ call ∈ pendingCalls before,
      retainedResultIds after.history = retainedResultIds before.history ++ [call.id] ∧
      RetiredCall call.id after

/-- The timeout policy closes the whole admitted queue, in its original order.
This is distinct from the one-result contract for ordinary replies. -/
def BatchResultUpdate (before after : (State app)) : Prop :=
  retainedResultIds after.history = retainedResultIds before.history ++
    (pendingCalls before).map (·.id) ∧
  ∀ call ∈ pendingCalls before, RetiredCall call.id after

theorem appendNotExecuted_retained_ids (state : (State app)) (remaining : List (Call app)) :
    retainedResultIds (appendNotExecuted state remaining).history =
      retainedResultIds state.history ++ remaining.map (·.id) := by
  change retainedResultIds (remaining.foldl _ state).history = _
  induction remaining generalizing state with
  | nil => simp
  | cons call rest ih =>
    simpa [List.foldl_cons, appendResult_retained_ids, List.append_assoc] using
      ih (appendResult state call timeoutSkippedText true)

theorem cancelCalls_retained_ids (state : State app) (calls : List (Call app)) :
    retainedResultIds (cancelCalls state calls).history =
      retainedResultIds state.history ++ calls.map (·.id) := by
  change retainedResultIds (calls.foldl _ state).history = _
  induction calls generalizing state with
  | nil => simp
  | cons call rest ih =>
    simpa [List.foldl_cons, appendResult_retained_ids, List.append_assoc] using
      ih (appendResult state call cancelledCallText true)

private theorem results_cancel (state : State app) (calls : List (Call app))
    (valid : CallsValid state) (queue : pendingCalls state = calls) :
    BatchResultUpdate state (cancelCalls state calls) := by
  refine ⟨by simpa [queue] using cancelCalls_retained_ids state calls, ?_⟩
  intro call member
  exact ⟨valid.2.2 call member, by simp [pendingCalls, cancelCalls]⟩

theorem timeout_retained_ids (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (partialResult : Option ToolResult) :
    retainedResultIds (settleTimedOut state call remaining partialResult).history =
      retainedResultIds state.history ++ (call :: remaining).map (·.id) := by
  simp [settleTimedOut, appendNotExecuted_retained_ids, appendResult_retained_ids,
    List.append_assoc]

private theorem results_timeout (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (partialResult : Option ToolResult) (valid : CallsValid state)
    (phase : state.phase = .tool call remaining) :
    BatchResultUpdate state (settleTimedOut state call remaining partialResult) := by
  refine ⟨?_, ?_⟩
  · simpa [pendingCalls, phase] using timeout_retained_ids state call remaining partialResult
  · intro admitted member
    exact ⟨valid.2.2 admitted member, by simp [pendingCalls, settleTimedOut]⟩

private theorem result_append_update (state next : (State app)) (call : (Call app)) (remaining : List (Call app))
    (valid : CallsValid state) (queue : pendingCalls state = call :: remaining)
    (history : retainedResultIds next.history = retainedResultIds state.history ++ [call.id])
    (seen : next.seenCallIds = state.seenCallIds) (pending : pendingCalls next = remaining) :
    ResultUpdate state next := by
  have admitted := valid.2.2 call (by simp [queue])
  have distinct : (call.id :: remaining.map (·.id)).Nodup := by
    simpa only [queue, List.map_cons] using valid.2.1
  exact Or.inr ⟨call, by simp [queue], history,
    by simpa only [RetiredCall, seen, pending] using And.intro admitted (List.nodup_cons.mp distinct).1⟩

private theorem results_repair (state : (State app)) (kind : ResponseRepairKind) (message : String) :
    ResultUpdate state (repairTaskResponse state kind message) := by
  apply Or.inl
  unfold repairTaskResponse; split <;>
    simp [retainedResultIds, responseRepairMessage, stop]

private theorem results_model (state : (State app)) (observation : ModelObservation) :
    ResultUpdate state (consumeModel state observation) := by
  cases observation with
  | interrupted => exact Or.inl rfl
  | uncertain message => simp only [consumeModel]; unfold retryOrStop; split <;> exact Or.inl rfl
  | failure kind message =>
    cases kind <;> simp only [consumeModel]
    all_goals first | exact Or.inl rfl | exact results_repair _ _ _ | (unfold retryOrStop; split <;> exact Or.inl rfl)
  | success response =>
    cases usage : response.usage <;> cases reason : response.stop <;>
      simp only [consumeModel, reason, usage, accountUsage]
    all_goals repeat' first | (exact Or.inl rfl) | (exact results_repair _ _ _) | split
    all_goals apply Or.inl; exact assistant_retained_ids state response (by assumption)

private theorem results_summary (state : (State app)) (plan : SummaryPlan) (observation : ModelObservation) :
    ResultUpdate state (consumeSummary state plan observation) := by
  cases observation with
  | interrupted => exact Or.inl rfl
  | uncertain message => simp only [consumeSummary]; unfold retryOrStop; split <;> exact Or.inl rfl
  | failure kind message =>
    cases kind <;> simp only [consumeSummary]
    all_goals first | exact Or.inl rfl | (unfold retryOrStop; split <;> exact Or.inl rfl)
  | success response =>
    cases usage : response.usage <;> cases reason : response.stop <;>
      simp only [consumeSummary, reason, usage, accountUsage]
    all_goals repeat' first | (exact Or.inl rfl) | split | (unfold installSummary; dsimp only)

private theorem results_tool (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ToolObservation ToolResult) (valid : CallsValid state)
    (phase : state.phase = .tool call remaining) :
    ResultUpdate state (consumeTool state call remaining observation) ∨
      (¬ OrdinaryToolReply observation ∧ BatchResultUpdate state (consumeTool state call remaining observation)) := by
  cases observation <;> simp only [consumeTool, retainPartialArtifacts]
  case timedOut partialResult =>
    split
    · exact Or.inr ⟨id, results_timeout state call remaining partialResult valid phase⟩
    · exact Or.inl (Or.inl rfl)
  all_goals apply Or.inl
  all_goals repeat' first
    | (exact Or.inl rfl)
    | (exact result_append_update state _ call remaining valid (by simp [pendingCalls, phase])
        (appendResult_retained_ids _ call _ _) rfl rfl)
    | split

private theorem results_approval (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ApprovalObservation) (valid : CallsValid state)
    (phase : state.phase = .ask call remaining) :
    ResultUpdate state (consumeApproval state call remaining observation) ∨
      (¬ OrdinaryReply (.ask call) observation ∧ BatchResultUpdate state (consumeApproval state call remaining observation)) := by
  cases observation with
  | approved => exact Or.inl (Or.inl rfl)
  | interrupted =>
    exact Or.inr ⟨id, results_cancel state _ valid (by simp [pendingCalls, phase])⟩
  | denied =>
    exact Or.inl (result_append_update state _ call remaining valid (by simp [pendingCalls, phase])
      (appendResult_retained_ids _ call _ _) rfl rfl)

private theorem results_admitModel (state : (State app)) : ResultUpdate state (admitModel state) := by
  unfold admitModel
  repeat' first | (exact Or.inl rfl) | split | (unfold admitTask; dsimp only) | unfold admitSummary

private theorem results_control (state : (State app)) (calls : Option (List (Call app)))
    (observation : ControlObservation) (valid : CallsValid state)
    (queue : ∀ pending, calls = some pending → pendingCalls state = pending) :
    ResultUpdate state (consumeControl state calls observation) ∨
      (¬ OrdinaryReply (.control : Action app) observation ∧ BatchResultUpdate state (consumeControl state calls observation)) := by
  simp only [consumeControl]
  split
  · cases calls with
    | none => exact Or.inl (Or.inl rfl)
    | some calls =>
      exact Or.inr ⟨by simpa [OrdinaryReply] using (show observation.cancelled ≠ false from by simp_all),
        results_cancel state calls valid (queue calls rfl)⟩
  · apply Or.inl
    split
    · exact Or.inl rfl
    · cases calls with
      | none => exact results_admitModel state
      | some calls =>
        have pending := queue calls rfl
        cases calls with
        | nil => exact Or.inl rfl
        | cons call remaining =>
          dsimp only
          unfold admitTool
          split
          · split
            · exact Or.inl rfl
            · split
              · exact Or.inl rfl
              · exact result_append_update state _ call remaining valid pending
                  (appendResult_retained_ids _ call _ _) rfl rfl
          · exact Or.inl rfl

private def ResultNode (state : (State app)) (node : (HarnessF app) (State app)) : Prop :=
  ∀ response : Reply node.1, ResultUpdate state (node.2 response) ∨
    (¬ OrdinaryReply node.1 response ∧ BatchResultUpdate state (node.2 response))

theorem result_step_contract_all (state : (State app)) (valid : CallsValid state) :
    ∀ response : Reply (step state).1, ResultUpdate state ((step state).2 response) ∨
      (¬ OrdinaryReply (step state).1 response ∧ BatchResultUpdate state ((step state).2 response)) := by
  change ResultNode state (step state)
  cases phase : state.phase <;> simp only [step, phase]
  case stopped outcome => intro response; exact response.elim
  case controlModel =>
    intro response
    simpa only [ResultUpdate, BatchResultUpdate, RetiredCall, pendingCalls, advance] using
      results_control state none response valid (by simp)
  case controlTools calls =>
    intro response
    simpa only [ResultUpdate, BatchResultUpdate, RetiredCall, pendingCalls, advance] using
      results_control state (some calls) response valid
        (by intro _ equal; cases equal; simp [pendingCalls, phase])
  case ask call remaining =>
    intro response
    simpa only [ResultUpdate, BatchResultUpdate, RetiredCall, pendingCalls, advance] using
      results_approval state call remaining response valid phase
  case waiting delay => intro response; cases response <;> exact Or.inl (Or.inl rfl)
  case model =>
    by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts)) = true
    · erw [if_pos admitted]; exact fun response => Or.inl (results_model state response)
    · erw [if_neg admitted]; intro response; exact response.elim
  case summary =>
    cases pending : state.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts) && planValid state plan) = true
      · erw [if_pos admitted]; exact fun response => Or.inl (results_summary state plan response)
      · erw [if_neg admitted]; intro response; exact response.elim
  case tool call remaining =>
    by_cases admitted : (authorized state.config state.grant call && artifactAuthorized state call && decide (0 < state.toolDispatches) && decide (state.toolDispatches ≤ state.config.maxToolCalls)) = true
    · erw [if_pos admitted]
      intro response
      simpa only [OrdinaryReply, ordinary_tool_reply_map, ResultUpdate, BatchResultUpdate, RetiredCall, pendingCalls, advance] using
        results_tool state call remaining (response.map (app.render call.operation)) valid phase
    · erw [if_neg admitted]; intro response; exact response.elim

/-- The previous zero-or-one result contract continues to hold for every
ordinary reply. Settled timeout and cancellation have separate whole-batch contracts above. -/
theorem result_step_contract (state : (State app)) (valid : CallsValid state)
    (response : Reply (step state).1) (ordinary : OrdinaryReply (step state).1 response) :
    ResultUpdate state ((step state).2 response) := by
  rcases result_step_contract_all state valid response with original | timeout
  · exact original
  · exact (timeout.1 ordinary).elim

theorem result_history_preserved (state : (State app)) (calls : CallsValid state) (valid : ResultsValid state)
    (response : Reply (step state).1) : ResultsValid ((step state).2 response) := by
  rcases result_step_contract_all state calls response with (unchanged | appended) | timeout
  · refine ⟨unchanged ▸ valid.1, ?_⟩
    intro id member
    exact retired_call_preserved id state (valid.2 id (unchanged ▸ member)) response
  · obtain ⟨call, pending, history, retired⟩ := appended
    have fresh : call.id ∉ retainedResultIds state.history := by
      intro member
      exact (valid.2 call.id member).2 (List.mem_map.mpr ⟨call, pending, rfl⟩)
    refine ⟨history ▸ List.nodup_append.mpr ⟨valid.1, by simp, ?_⟩, ?_⟩
    · intro id previous other single equal
      have same : other = call.id := by simpa using single
      subst other
      subst id
      exact fresh previous
    · intro id member
      rw [history] at member
      rcases List.mem_append.mp member with previous | latest
      · exact retired_call_preserved id state (valid.2 id previous) response
      · have same : id = call.id := by simpa using latest
        exact same ▸ retired
  · obtain ⟨_, history, retired⟩ := timeout
    have disjoint : List.Disjoint (retainedResultIds state.history) ((pendingCalls state).map (·.id)) := by
      intro id old pending
      exact (valid.2 id old).2 pending
    refine ⟨history ▸ List.nodup_append.mpr ⟨valid.1, calls.2.1, ?_⟩, ?_⟩
    · intro old oldMember pending pendingMember equal
      subst pending
      exact disjoint oldMember pendingMember
    intro id member
    rw [history] at member
    rcases List.mem_append.mp member with previous | latest
    · exact retired_call_preserved id state (valid.2 id previous) response
    · obtain ⟨call, pending, equal⟩ := List.mem_map.mp latest
      exact equal ▸ retired call pending

/-- Raw retained tool-result IDs are globally unique, belong to admitted calls,
and are no longer pending. This includes policy/approval denials and tool errors;
it does not assert that an external effect succeeded or happened only once. -/
theorem reachable_result_correlation {id : String} {config : Config} {task : String} {state : (State app)}
    (reachable : Reachable id config task state) : ResultsValid state := by
  induction reachable with
  | initial => simp [ResultsValid, retainedResultIds, init, resultId_text]
  | next previous response ih => exact result_history_preserved _ (reachable_calls previous) ih response

private theorem paired_append_text (messages : List Message) (pending : List String) (text : String)
    (closed : pairedMessages pending messages = true) :
    pairedMessages pending (messages ++ [{role := "user", content := #[textBlock text]}]) = true := by
  induction messages generalizing pending with
  | nil =>
    cases pending with
    | nil => rfl
    | cons id rest => simp [pairedMessages] at closed
  | cons message rest ih =>
    by_cases user : (message.role == "user") = true
    · cases parsed : userResultIds message.content.toList false with
      | error error => simp [pairedMessages, user, parsed] at closed
      | ok ids =>
        simp only [pairedMessages, user, if_true, parsed, Bool.and_eq_true] at closed
        simp only [List.cons_append, pairedMessages, user, if_true, parsed,
          closed.1, Bool.true_and]
        exact ih [] closed.2
    · by_cases assistant : (message.role == "assistant" && pending.isEmpty) = true
      · cases parsed : parseModelContent message.content with
        | error error => simp [pairedMessages, user, assistant, parsed] at closed
        | ok result =>
          obtain ⟨calls, answer⟩ := result
          simp only [pairedMessages, user, Bool.false_eq_true, if_false, assistant, if_true, parsed,
            Bool.and_eq_true] at closed
          simp only [List.cons_append, pairedMessages, user, Bool.false_eq_true, if_false, assistant,
            if_true, parsed, closed.1, Bool.true_and]
          exact ih (calls.map (·.id)) closed.2
      · simp [pairedMessages, user, assistant] at closed

theorem closed_history_append_text (messages : List Message) (text : String)
    (closed : historyValid messages = true) :
    historyValid (messages ++ [{role := "user", content := #[textBlock text]}]) = true := by
  cases messages with
  | nil => simp [historyValid] at closed
  | cons first rest =>
    have both : (first.role == "user") = true ∧ pairedMessages [] (first :: rest) = true := by
      simpa only [historyValid, Bool.and_eq_true] using closed
    change ((first.role == "user") && pairedMessages [] ((first :: rest) ++ _)) = true
    simp only [both.1, Bool.true_and]
    exact paired_append_text (first :: rest) [] text both.2

/-- The actual summary request is also closed: its validated source is followed
by one ordinary user instruction, never by an unresolved tool-result placeholder. -/
theorem emitted_summary_history_valid (state : (State app)) (request : ModelRequest)
    (phase : state.phase = .summary) (emitted : (step state).1 = .model request) :
    historyValid request.messages = true := by
  obtain ⟨plan, _, equal, valid, _⟩ := emitted_summary_admitted state request phase emitted
  subst request
  have source : historyValid (summarySource state plan) = true := by
    simp only [planValid, Bool.and_eq_true] at valid
    exact valid.1.1.2
  exact closed_history_append_text (summarySource state plan) summaryInstruction source

end Harness
