import Harness.Proofs.ApplicationOperations
import Harness.Proofs.ApplicationObservations
import Harness.Proofs.Transcript

/-! Faithful model-facing presentation of the actual shared transition. Extraction reads raw
history blocks; the specification separately names normalization, errors and skipped calls. It
makes no claim that adapter observations are true, nor that partial output establishes settlement. -/
namespace Harness
open Lean ExceptRules
variable {app : Application}

structure VisibleToolResult where
  id : String
  content : String
  isError : Bool
  deriving Repr, DecidableEq

/-- Independent observation of what a model-facing history actually contains. -/
def visibleToolResult? (block : Json) : Option VisibleToolResult := do
  if (contentString block "type").toOption != some "tool_result" then none else do
    let id ← (contentString block "tool_use_id").toOption
    let content ← (contentString block "content").toOption
    let isError ← (block.getObjValAs? Bool "is_error").toOption
    return {id, content, isError}

def visibleToolResults (history : List Message) : List VisibleToolResult :=
  history.flatMap fun message => message.content.toList.filterMap visibleToolResult?

theorem visible_generated_result (call : Call app) (text : String) (isError : Bool) :
    visibleToolResult? (Json.mkObj [("type", toJson "tool_result"), ("tool_use_id", toJson call.id),
      ("content", toJson text), ("is_error", toJson isError)]) = some ⟨call.id, text, isError⟩ := rfl

theorem append_result_visible (state : State app) (call : Call app) (text : String) (isError : Bool) :
    visibleToolResults (appendResult state call text isError).history =
      visibleToolResults state.history ++ [⟨call.id, text, isError⟩] := by
  have history : state.history = state.history.reverse.reverse := by simp
  cases reversed : state.history.reverse with
  | nil =>
    have empty : state.history = [] := by simpa [reversed] using history
    simp [appendResult, empty, visibleToolResults, visible_generated_result]
  | cons last rest =>
    have original : state.history = rest.reverse ++ [last] := by simpa [reversed] using history
    simp only [appendResult, reversed]
    split <;> simp [visibleToolResults, List.reverse_cons, original, visible_generated_result,
      List.flatMap_append, List.filterMap_append, List.append_assoc]

theorem skipped_results_visible (state : State app) (remaining : List (Call app)) :
    visibleToolResults (appendNotExecuted state remaining).history =
      visibleToolResults state.history ++ remaining.map (fun call => ⟨call.id, timeoutSkippedText, true⟩) := by
  unfold appendNotExecuted
  suffices ∀ before : State app,
      visibleToolResults (remaining.foldl (fun s call => appendResult s call timeoutSkippedText true) before).history =
      visibleToolResults before.history ++ remaining.map (fun call => ⟨call.id, timeoutSkippedText, true⟩) from this state
  induction remaining with
  | nil => intro before; simp
  | cons call rest ih =>
    intro before
    simp [List.foldl_cons, ih, append_result_visible, List.append_assoc]

/-- Specification of the new blocks only. Successful data passes through unchanged unless
artifact registration rejects it; local timeout explicitly removes exit/hash assertions. -/
def toolPresentation (state : State app) (call : Call app) (remaining : List (Call app)) :
    ToolObservation ToolResult → List VisibleToolResult
  | .success result =>
    match registerArtifacts state.config state.artifacts result.artifacts with
    | .ok _ => [⟨call.id, (toJson result).compress,
        match result.exitCode with | some code => code != 0 | none => false⟩]
    | .error message =>
      let text := boundedResultText
        (s!"Artifact references rejected: {message}\n" ++ result.text) state.config.maxToolOutputBytes
      let normalized := {result with artifacts := #[], text}
      [⟨call.id, (toJson normalized).compress, true⟩]
  | .failure message => [⟨call.id, message, true⟩]
  | .timedOut output =>
    if settledTimeoutEligible state call then
      [⟨call.id, (toJson (timeoutResultAndArtifacts state output).1).compress, true⟩] ++
        remaining.map (fun queued => ⟨queued.id, timeoutSkippedText, true⟩)
    else []
  | .interrupted _ _ | .uncertain _ _ => []

theorem consume_tool_visible (state : State app) (call : Call app) (remaining : List (Call app))
    (observation : ToolObservation ToolResult) :
    visibleToolResults (consumeTool state call remaining observation).history =
      visibleToolResults state.history ++ toolPresentation state call remaining observation := by
  cases observation <;> simp only [consumeTool, toolPresentation]
  case success result =>
    cases registered : registerArtifacts state.config state.artifacts result.artifacts <;>
      simp [append_result_visible]
    all_goals rfl
  case failure message => exact append_result_visible _ _ _ _
  case timedOut output =>
    split
    · simp [settleTimedOut, skipped_results_visible, append_result_visible, List.append_assoc]
    · simp [stop]
  all_goals simp [stop, retainPartialArtifacts]
  all_goals repeat' first | rfl | split

/-- The theorem concerns the actual dependent reply supplied to `step`, not a second execution
loop. Every observed block is exactly the application's rendering under shared normalization. -/
theorem emitted_tool_visible (state : State app) (call : Call app) (remaining : List (Call app))
    (continuation : ToolObservation (app.Result call.operation) → State app)
    (phase : state.phase = .tool call remaining)
    (emitted : step state = ⟨.tool call, continuation⟩)
    (observation : ToolObservation (app.Result call.operation)) :
    visibleToolResults (continuation observation).history =
      visibleToolResults state.history ++
        toolPresentation state call remaining (observation.map (app.render call.operation)) := by
  simp only [step, phase] at emitted
  by_cases admitted : (authorized state.config state.grant call && artifactAuthorized state call &&
      decide (0 < state.toolDispatches) && decide (state.toolDispatches ≤ state.config.maxToolCalls)) = true
  · erw [if_pos admitted] at emitted
    have same : (fun r => advance (consumeTool state call remaining (r.map (app.render call.operation)))) = continuation :=
      eq_of_heq (Sigma.mk.inj emitted).2
    rw [← same]
    exact consume_tool_visible state call remaining _
  · erw [if_neg admitted] at emitted
    cases emitted

/-- Shared timeout normalization never asserts a process exit or file hash. -/
theorem timeout_clears_unestablished_metadata (state : State app) (output : Option ToolResult) :
    (timeoutResultAndArtifacts state output).1.exitCode = none ∧
    (timeoutResultAndArtifacts state output).1.sha256 = none := by
  unfold timeoutResultAndArtifacts
  dsimp only
  split <;> simp [timeoutResult]

/-- Closing the skipped suffix neither dispatches work nor debits its budget. -/
theorem timeout_skips_without_dispatch (state : State app) (call : Call app)
    (remaining : List (Call app)) (output : Option ToolResult) :
    (settleTimedOut state call remaining output).toolDispatches = state.toolDispatches ∧
    (settleTimedOut state call remaining output).modelAttempts = state.modelAttempts ∧
    (settleTimedOut state call remaining output).phase = .controlModel := ⟨rfl, rfl, rfl⟩

/-- App-specific representation and actual model-visible delivery compose through `step`. -/
theorem emitted_success_faithful (laws : ApplicationLaws app) (state : State app)
    (call : Call app) (remaining : List (Call app))
    (continuation : ToolObservation (app.Result call.operation) → State app)
    (phase : state.phase = .tool call remaining)
    (emitted : step state = ⟨.tool call, continuation⟩)
    (value : app.Result call.operation) (validOp : laws.ValidOperation call.operation)
    (validResult : laws.ValidResult call.operation value) (artifacts : List ArtifactRef)
    (registered : registerArtifacts state.config state.artifacts (app.render call.operation value).artifacts = .ok artifacts) :
    laws.Rendered call.operation value (app.render call.operation value) ∧
    visibleToolResults (continuation (.success value)).history = visibleToolResults state.history ++
      [⟨call.id, (toJson (app.render call.operation value)).compress,
        match (app.render call.operation value).exitCode with | some code => code != 0 | none => false⟩] := by
  refine ⟨laws.render_faithful call.operation value validOp validResult, ?_⟩
  simpa only [ToolObservation.map, toolPresentation, registered] using
    emitted_tool_visible state call remaining continuation phase emitted (.success value)

theorem cancellation_visible (state : State app) (calls : List (Call app)) :
    visibleToolResults (cancelCalls state calls).history = visibleToolResults state.history ++
      calls.map (fun call => ⟨call.id, cancelledCallText, true⟩) := by
  unfold cancelCalls
  suffices ∀ before : State app,
      visibleToolResults (calls.foldl (fun s call => appendResult s call cancelledCallText true) before).history =
      visibleToolResults before.history ++ calls.map (fun call => ⟨call.id, cancelledCallText, true⟩) from this state
  induction calls with
  | nil => intro before; simp
  | cons call rest ih => intro before; simp [List.foldl_cons, ih, append_result_visible, List.append_assoc]

theorem cancelled_control_visible (state : State app) (calls : Option (List (Call app)))
    (observation : ControlObservation) (cancelled : observation.cancelled = true) :
    visibleToolResults (consumeControl state calls observation).history = visibleToolResults state.history ++
      (calls.getD []).map (fun call => ⟨call.id, cancelledCallText, true⟩) := by
  simp only [consumeControl, cancelled, ↓reduceIte]
  exact cancellation_visible state _

theorem denied_approval_visible (state : State app) (call : Call app) (remaining : List (Call app)) :
    visibleToolResults (consumeApproval state call remaining .denied).history =
      visibleToolResults state.history ++ [⟨call.id, "not executed: approval denied", true⟩] :=
  append_result_visible _ _ _ _

theorem cancelled_approval_visible (state : State app) (call : Call app) (remaining : List (Call app)) :
    visibleToolResults (consumeApproval state call remaining .interrupted).history =
      visibleToolResults state.history ++ (call :: remaining).map (fun c => ⟨c.id, cancelledCallText, true⟩) :=
  cancellation_visible _ _

theorem denied_policy_visible (state : State app) (call : Call app) (remaining : List (Call app))
    (budget : state.toolDispatches < state.config.maxToolCalls)
    (denied : (authorized state.config state.grant call && artifactAuthorized state call) = false)
    (notAsked : (policy state.config call == .ask && artifactAuthorized state call) = false) :
    visibleToolResults (admitTool state call remaining).history = visibleToolResults state.history ++
      [⟨call.id, "not executed: policy denied", true⟩] ∧
    (admitTool state call remaining).toolDispatches = state.toolDispatches := by
  simp only [admitTool, budget, denied, notAsked, ↓reduceIte, Bool.false_eq_true]
  exact ⟨append_result_visible _ _ _ _, rfl⟩

end Harness
