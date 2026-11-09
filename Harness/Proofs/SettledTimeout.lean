import Harness.Proofs.RawPrefix
import Harness.Proofs.RecoveryLedger

/-!
Settled local timeout closes the admitted batch as ordered errors, retires its
identities, and returns through control before another request. Ordinary replies
retain their single-head queue contract. Settlement of OS resources is an adapter
assumption; neither rollback nor a target exit status is asserted here.
-/

namespace Harness

variable {app : Application}
open Lean

private def resultError? (block : Json) : Option (String × Bool) := do
  if (block.getObjValAs? String "type").toOption != some "tool_result" then none else do
    let id ← (block.getObjValAs? String "tool_use_id").toOption
    let isError ← (block.getObjValAs? Bool "is_error").toOption
    pure (id, isError)

/-- Independent extraction of result identities and error flags from raw JSON. -/
def retainedResultErrors (history : List Message) : List (String × Bool) :=
  history.flatMap fun message => message.content.toList.filterMap resultError?

private theorem result_error_generated (call : (Call app)) (text : String) (isError : Bool) :
    resultError? (Json.mkObj [("type", toJson "tool_result"), ("tool_use_id", toJson call.id),
      ("content", toJson text), ("is_error", toJson isError)]) = some (call.id, isError) := by
  cases isError <;> rfl

private theorem append_result_errors (state : (State app)) (call : (Call app)) (text : String) (isError : Bool) :
    retainedResultErrors (appendResult state call text isError).history =
      retainedResultErrors state.history ++ [(call.id, isError)] := by
  have history : state.history = state.history.reverse.reverse := by simp
  cases reversed : state.history.reverse with
  | nil =>
    have empty : state.history = [] := by simpa [reversed] using history
    simp [appendResult, empty, retainedResultErrors, result_error_generated]
  | cons last rest =>
    have original : state.history = rest.reverse ++ [last] := by simpa [reversed] using history
    simp only [appendResult, reversed]
    split <;> simp [retainedResultErrors, List.reverse_cons, original,
      List.flatMap_append, List.filterMap_append, List.append_assoc, result_error_generated]

private theorem append_not_executed_errors (state : (State app)) (remaining : List (Call app)) :
    retainedResultErrors (appendNotExecuted state remaining).history =
      retainedResultErrors state.history ++ remaining.map (fun call => (call.id, true)) := by
  change retainedResultErrors (remaining.foldl _ state).history = _
  induction remaining generalizing state with
  | nil => simp
  | cons call rest ih =>
    simpa [List.foldl_cons, append_result_errors, List.append_assoc] using
      ih (appendResult state call timeoutSkippedText true)

theorem timeout_ordered_errors (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (partialResult : Option ToolResult) (eligible : settledTimeoutEligible state call = true) :
    retainedResultErrors (consumeTool state call remaining (.timedOut partialResult)).history =
      retainedResultErrors state.history ++ (call :: remaining).map (fun call => (call.id, true)) := by
  simp [consumeTool, eligible, settleTimedOut, append_not_executed_errors,
    append_result_errors, List.append_assoc]

/-- Exhaustive queue disposition: ordinary settlement consumes one head,
eligible timeout closes the batch, invalid timeout hard-stops, and only genuinely
uncertain replies enter the recoverable stop. -/
theorem tool_reply_queue_disposition (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (response : ToolObservation (app.Result call.operation)) :
    (OrdinaryToolReply response ∧ Recovery.replyIsUncertain (.tool call) response = false ∧
      (consumeTool state call remaining (response.map (app.render call.operation))).phase = .controlTools remaining) ∨
    (∃ partialResult, response = .timedOut partialResult ∧
      ((settledTimeoutEligible state call = true ∧
        (consumeTool state call remaining (response.map (app.render call.operation))).phase = .controlModel) ∨
       (settledTimeoutEligible state call = false ∧
        (consumeTool state call remaining (response.map (app.render call.operation))).phase = .stopped (.failure invalidTimeoutText)))) ∨
    (Recovery.replyIsUncertain (.tool call) response = true ∧
      ∃ message, (consumeTool state call remaining (response.map (app.render call.operation))).phase = .stopped (.recoveryRequired message)) := by
  cases response <;> simp only [ToolObservation.map]
  case success result =>
    apply Or.inl
    refine ⟨trivial, rfl, ?_⟩
    simp only [consumeTool]; split <;> rfl
  case failure message => exact Or.inl ⟨trivial, rfl, rfl⟩
  case interrupted message partialResult => exact Or.inr (Or.inr ⟨rfl, _, rfl⟩)
  case uncertain message partialResult => exact Or.inr (Or.inr ⟨rfl, _, rfl⟩)
  case timedOut partialResult =>
    apply Or.inr; apply Or.inl
    refine ⟨partialResult, rfl, ?_⟩
    cases eligible : settledTimeoutEligible state call <;>
      simp [consumeTool, eligible, settleTimedOut, stop]

/-- No reservation is refunded or spent by settlement; summary/source state and
seen identities are unchanged. Only the admitted batch's result history and
validated artifact registry may grow. -/
theorem timeout_state_frame (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (partialResult : Option ToolResult) (eligible : settledTimeoutEligible state call = true) :
    let next := consumeTool state call remaining (.timedOut partialResult)
    next.phase = .controlModel ∧ next.grant = none ∧
    next.config = state.config ∧ next.modelAttempts = state.modelAttempts ∧
    next.toolDispatches = state.toolDispatches ∧ next.responseRepairs = state.responseRepairs ∧
    next.retryCount = state.retryCount ∧ next.seenCallIds = state.seenCallIds ∧
    next.activeView = state.activeView ∧ next.pendingSummary = state.pendingSummary ∧
    next.summaries = state.summaries ∧ next.knownInputTokens = state.knownInputTokens ∧
    next.knownOutputTokens = state.knownOutputTokens ∧ next.unknownUsage = state.unknownUsage := by
  simp [consumeTool, eligible, settleTimedOut]

theorem timeout_result_has_no_exit_or_hash (state : (State app)) (partialResult : Option ToolResult) :
    (timeoutResultAndArtifacts state partialResult).1.exitCode = none ∧
      (timeoutResultAndArtifacts state partialResult).1.sha256 = none := by
  unfold timeoutResultAndArtifacts
  dsimp only
  split <;> simp [timeoutResult]

theorem invalid_timeout_stops (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (partialResult : Option ToolResult) (invalid : settledTimeoutEligible state call = false) :
    consumeTool state call remaining (.timedOut partialResult) =
      stop state (.failure invalidTimeoutText) := by
  simp [consumeTool, invalid]

/-- Even a forged timeout for another profile/tool can only stop. An admitted
timeout cannot bypass the next cancellation/deadline observation. -/
theorem timeout_next_action (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (partialResult : Option ToolResult) :
    (step (advance (consumeTool state call remaining (.timedOut partialResult)))).1 = .control ∨
    (step (advance (consumeTool state call remaining (.timedOut partialResult)))).1 =
      .finish (.failure invalidTimeoutText) := by
  simp only [consumeTool]; split <;> simp [settleTimedOut, stop, step, advance]

/-- Every skipped identity was already admitted and is now retired. Future
ordinary execution cannot dispatch it, even after another model response. -/
theorem timeout_suffix_never_dispatches (state : (State app)) (call skipped : (Call app))
    (remaining : List (Call app)) (partialResult : Option ToolResult)
    (valid : CallsValid state) (phase : state.phase = .tool call remaining)
    (eligible : settledTimeoutEligible state call = true) (member : skipped ∈ remaining)
    {events : List (ObservedStep app)} {last : (State app)}
    (trace : ExecutionTrace (advance (consumeTool state call remaining (.timedOut partialResult))) events last) :
    (step last).1 ≠ .tool skipped := by
  apply retired_call_never_dispatches trace skipped
  constructor
  · simpa [consumeTool, eligible, settleTimedOut, advance] using
      valid.2.2 skipped (by simp [pendingCalls, phase, member])
  · simp [consumeTool, eligible, settleTimedOut, advance, pendingCalls]

end Harness

namespace Harness.Recovery

variable {app : Application}

theorem timeout_reply_settled (call : (Call app)) (partialResult : Option (app.Result call.operation)) :
    replyIsUncertain (.tool call) (.timedOut partialResult) = false := rfl

/-- Durable settlement clears both the pending intent and the saved recovery
position. This includes rejected timeout observations that hard-stop the core. -/
theorem settled_completion_has_no_target (cursor : (Cursor app))
    (response : Reply (step cursor.state).1)
    (settled : replyIsUncertain (step cursor.state).1 response = false) :
    (complete cursor response).pending = false ∧
    (complete cursor response).suspended = none ∧
    (complete cursor response).editWitness = none ∧
    target (complete cursor response) = none := by
  simp [complete, settled, target]

end Harness.Recovery
