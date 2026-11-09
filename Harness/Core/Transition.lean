import Harness.Core.Effects
import Harness.Core.ModelResponse
import Harness.Core.Artifacts

/-!
Defines `step : State app → HarnessF app (State app)`, the pure, total coalgebra executed by the CLI. It
interprets model, summary, tool, approval, wait and control observations. Before emitting work it
reserves attempt and dispatch budgets, checks context admission and authorization, and selects
compaction at tool-batch boundaries. Every consumed observation advances `nextId`; all IO happens in
adapters.
-/

namespace Harness
open Lean

variable {app : Application}

/-- Each consumed observation advances the serializable operation identity. -/
def advance (s : State app) : State app := { s with nextId := s.nextId + 1 }

def appendResult (s : State app) (call : Call app) (text : String) (isError : Bool) : State app :=
  let block := Json.mkObj [("type", toJson "tool_result"), ("tool_use_id", toJson call.id),
    ("content", toJson text), ("is_error", toJson isError)]
  let history := match s.history.reverse with
    | last :: rest => if last.role == "user" then
        ( {last with content := last.content.push block} :: rest).reverse
      else s.history ++ [{role := "user", content := #[block]}]
    | [] => [{role := "user", content := #[block]}]
  {s with history, grant := none}

def accountUsage (s : State app) (usage : Option Usage) : State app :=
  match usage with
  | some u => {s with knownInputTokens := s.knownInputTokens + u.inputTokens, knownOutputTokens := s.knownOutputTokens + u.outputTokens}
  | none => {s with unknownUsage := s.unknownUsage + 1}

def retryOrStop (s : State app) (message : String) : State app :=
  if s.retryCount < s.config.maxRetries && s.modelAttempts < s.config.maxModelAttempts then
    {s with retryCount := s.retryCount + 1, phase := .waiting (1000 * (s.retryCount + 1))}
  else stop s (.failure message)

/-- Only task-response repair uses this budget; summary and transport retries keep
  their existing semantics. The fixed feedback never reflects untrusted arguments. -/
inductive ResponseRepairKind where
  | invalidBatch | truncated | malformed
  deriving Repr, BEq, DecidableEq

def responseRepairText : ResponseRepairKind → String
  | .invalidBatch =>
    "[Harness validation feedback] The previous response's complete tool batch was rejected. No calls from that response executed. Return a new complete batch using unique call IDs, documented tools and fields, valid argument types and bounds, and the documented application constraints. Read or query current information first when an operation requires it."
  | .truncated =>
    "[Harness validation feedback] The previous response was truncated. No calls from that response executed. Return a smaller complete response with fewer or shorter tool calls. Do not assume that any proposed edit ran."
  | .malformed =>
    "[Harness validation feedback] The previous response was incomplete or malformed. No calls from that response executed. Return a smaller complete response using the documented message and tool schemas."

def responseRepairMessage (kind : ResponseRepairKind) : Message :=
  {role := "user", content := #[textBlock (responseRepairText kind)]}

/-- A repair cannot authorize a call or refund an attempt. The next ordinary
control observation checks cancellation/deadline before fresh model admission.
Rejected assistant content remains in journal evidence, outside accepted history. -/
def repairTaskResponse (s : State app) (kind : ResponseRepairKind) (failure : String) : State app :=
  if s.responseRepairs < s.config.maxResponseRepairs &&
      s.modelAttempts < s.config.maxModelAttempts then
    {s with history := s.history ++ [responseRepairMessage kind], phase := .controlModel, responseRepairs := s.responseRepairs + 1, grant := none}
  else stop s (.failure failure)

def consumeModel (s : State app) : ModelObservation → State app
  | .interrupted => stop {s with unknownUsage := s.unknownUsage + 1} .cancelled
  | .uncertain message => retryOrStop {s with unknownUsage := s.unknownUsage + 1} message
  | .failure kind message =>
    let s := {s with unknownUsage := s.unknownUsage + 1}
    match kind with
    | .rateLimit => retryOrStop s message
    | .transport => retryOrStop s message
    | .malformed => repairTaskResponse s .malformed message
    | _ => stop s (.failure message)
  | .success response =>
    let s := accountUsage s response.usage
    match response.stop with
    | .endTurn =>
      match validateModelResponse response with
      | .error message => stop s (.failure s!"invalid model response: {message}")
      | .ok () =>
        if response.calls.isEmpty then
          stop {s with history := s.history ++ [{role := "assistant", content := response.content}], retryCount := 0} (.final response.text)
        else stop s (.failure "end-turn response included tool calls")
    | .toolUse =>
      match validateModelResponse response with
      | .error message => stop s (.failure s!"invalid model response: {message}")
      | .ok () =>
        match validateBatch s.config s.seenCallIds response.calls app with
        | .error message => repairTaskResponse s .invalidBatch s!"invalid tool batch: {message}"
        | .ok calls =>
          {s with history := s.history ++ [{role := "assistant", content := response.content}], phase := .controlTools calls, seenCallIds := s.seenCallIds ++ calls.map (·.id), retryCount := 0, grant := none}
    | .contextOverflow => stop s (.limit "provider context allowance exceeded")
    | .maxTokens => repairTaskResponse s .truncated "model output truncated; no tool calls executed"
    | .refusal => stop s (.failure "model refusal")
    | .other => stop s (.failure "unsupported model stop reason")

/-- The proposed active view, retaining its source metadata and complete response. -/
def summaryCandidate (s : State app) (plan : SummaryPlan) (response : ModelResponse) : State app :=
  {s with activeView := some (summaryView plan response), pendingSummary := none, summaries := s.summaries ++ [{plan, response}], phase := .controlModel, retryCount := 0, grant := none}

/-- A summary becomes an active view only after complete response validation and
admission of the reconstructed next task request. Raw history is untouched. -/
def installSummary (s : State app) (plan : SummaryPlan) (response : ModelResponse) : State app :=
  let candidate := summaryCandidate s plan response
  if contextAdmitted candidate && historyValid (activeMessages candidate) then candidate
  else stop s (.limit "compacted context exceeds allowance or has invalid tool pairing")

def consumeSummary (s : State app) (plan : SummaryPlan) : ModelObservation → State app
  | .interrupted => stop {s with unknownUsage := s.unknownUsage + 1} .cancelled
  | .uncertain message => retryOrStop {s with unknownUsage := s.unknownUsage + 1} message
  | .failure kind message =>
    let s := {s with unknownUsage := s.unknownUsage + 1}
    match kind with
    | .rateLimit | .transport => retryOrStop s message
    | _ => stop s (.failure message)
  | .success response =>
    let s := accountUsage s response.usage
    match response.stop with
    | .endTurn =>
      match validateModelResponse response with
      | .error message => stop s (.failure s!"invalid summary response: {message}")
      | .ok () =>
        if !response.calls.isEmpty || response.text.isEmpty then
          stop s (.failure "summary must contain nonempty text and no tool calls")
        else if response.text.utf8ByteSize > s.config.maxSummaryBytes then
          stop s (.limit "summary exceeds configured byte allowance")
        else installSummary s plan response
    | .toolUse => stop s (.failure "summary attempted tool use; no tools executed")
    | .contextOverflow => stop s (.limit "provider context allowance exceeded during compaction")
    | .maxTokens => stop s (.failure "summary output truncated; previous context retained")
    | .refusal => stop s (.failure "summary refusal")
    | .other => stop s (.failure "unsupported summary stop reason")

/-- Clip a valid string at a UTF-8 boundary without consulting the IO adapter. -/
def boundedResultText (text : String) (maximum : Nat) : String :=
  let bytes := text.toUTF8.extract 0 maximum
  ((List.range 4).findSome? fun removed =>
    String.fromUTF8? (bytes.extract 0 (bytes.size - removed))).getD ""

/-- Only the frozen sandbox process interface may report settled local timeout.
The physical settlement claim remains an adapter contract, not a core theorem. -/
def settledTimeoutEligible (s : State app) (call : Call app) : Bool :=
  app.settledTimeout s.config call.operation

def timeoutResultText : String :=
  "Command time limit reached; the sandboxed attempt has stopped. Partial effects may remain. Inspect the workspace and retained output before requesting more work."

def timeoutSkippedText : String :=
  "not executed: previous command timed out; inspect its partial effects before requesting more work"

def invalidTimeoutText : String :=
  "invalid settled-timeout observation for this tool or execution profile; prior effects are not established"

/-- A wrapper status or file hash is not evidence of the interrupted command's
exit code or final file contents. Retain only bounded text and artifact metadata. -/
def timeoutResult (s : State app) (partialResult : Option ToolResult) : ToolResult :=
  let partialResult := partialResult.getD {text := ""}
  {partialResult with
    text := boundedResultText (timeoutResultText ++ "\n" ++ partialResult.text) s.config.maxToolOutputBytes
    exitCode := none
    sha256 := none}

/-- Failed metadata validation does not change a known settled attempt into
uncertain execution; it withholds the references and reports retention failure. -/
def timeoutResultAndArtifacts (s : State app) (partialResult : Option ToolResult) :
    ToolResult × List ArtifactRef :=
  let result := timeoutResult s partialResult
  match registerArtifacts s.config s.artifacts result.artifacts with
  | .ok artifacts => (result, artifacts)
  | .error message =>
    ({result with artifacts := #[], text := boundedResultText (s!"Artifact references rejected: {message}\n" ++ result.text) s.config.maxToolOutputBytes},
      s.artifacts)

/-- Close the finite suffix in admitted order, without dispatching any call.
Only history and the one-shot grant change. -/
def appendNotExecuted (s : State app) (remaining : List (Call app)) : State app :=
  {s with
    history := (remaining.foldl (fun state call => appendResult state call timeoutSkippedText true) s).history
    grant := none}

def settleTimedOut (s : State app) (call : Call app) (remaining : List (Call app))
    (partialResult : Option ToolResult) : State app :=
  let retained := timeoutResultAndArtifacts s partialResult
  {s with
    history := (appendNotExecuted (appendResult s call (toJson retained.1).compress true) remaining).history
    artifacts := retained.2
    phase := .controlModel
    grant := none}

def consumeTool (s : State app) (call : Call app) (remaining : List (Call app)) : ToolObservation ToolResult → State app
  | .success r =>
    match registerArtifacts s.config s.artifacts r.artifacts with
    | .error message =>
      let text := boundedResultText
        (s!"Artifact references rejected: {message}\n" ++ r.text) s.config.maxToolOutputBytes
      let retained := {r with artifacts := #[], text}
      {appendResult s call (toJson retained).compress true with phase := .controlTools remaining}
    | .ok artifacts =>
      let error := match r.exitCode with | some n => n != 0 | none => false
      {appendResult {s with artifacts} call (toJson r).compress error with phase := .controlTools remaining}
  | .failure message => {appendResult s call message true with phase := .controlTools remaining}
  | .timedOut partialResult =>
    if settledTimeoutEligible s call then settleTimedOut s call remaining partialResult
    else stop s (.failure invalidTimeoutText)
  | .interrupted message partialResult =>
    stop (retainPartialArtifacts s partialResult) (.recoveryRequired s!"tool interrupted; effects may be partial: {message}")
  | .uncertain message partialResult => stop (retainPartialArtifacts s partialResult) (.recoveryRequired message)

/-- These calls were admitted but had not been dispatched when cancellation was
observed. Closing their transcript positions is not an execution or a refund. -/
def cancelledCallText : String :=
  "Not executed: the turn was cancelled before this call was dispatched."

def cancelCalls (s : State app) (calls : List (Call app)) : State app :=
  {s with
    history := (calls.foldl (fun state call => appendResult state call cancelledCallText true) s).history,
    phase := .stopped .cancelled, grant := none}

def consumeApproval (s : State app) (call : Call app) (remaining : List (Call app)) : ApprovalObservation → State app
  | .approved => {s with grant := some call, phase := .controlTools (call :: remaining)}
  | .denied => {appendResult s call "not executed: approval denied" true with phase := .controlTools remaining}
  | .interrupted => cancelCalls s (call :: remaining)

def consumeWait (s : State app) : WaitObservation → State app
  | .elapsed => {s with phase := .controlModel}
  | .interrupted => stop s .cancelled

/-- Reservation is part of the explicit state before the task action is emitted. -/
def admitTask (s : State app) : State app :=
  if s.modelAttempts < s.config.maxModelAttempts then
    let reserved := {s with modelAttempts := s.modelAttempts + 1, phase := .model}
    if contextAdmitted reserved then
      if historyValid (modelRequest reserved).messages then
        reserved
      else stop s (.failure "active context has invalid tool pairing")
    else stop s (.limit "context allowance exhausted")
  else stop s (.limit "model attempt ceiling exhausted")

def admitSummary (s : State app) (plan : SummaryPlan) : State app :=
  if s.modelAttempts < s.config.maxModelAttempts then
    if planValid s plan then
      {s with modelAttempts := s.modelAttempts + 1, phase := .summary, pendingSummary := some plan, grant := none}
    else stop s (.limit "no admissible compaction source and suffix")
  else stop s (.limit "model attempt ceiling exhausted")

/-- Called only at the boundary after a complete tool batch in reachable states.
Retries retain their exact pending summary source; no summary runs amid a batch. -/
def admitModel (s : State app) : State app :=
  match s.pendingSummary with
  | some plan => admitSummary s plan
  | none =>
    if wantsCompaction s then
      match planCompaction s with
      | some plan => admitSummary s plan
      | none => admitTask s
    else admitTask s

/-- A successful grant is consumed by exactly this operation; it is never reused. -/
def admitTool (s : State app) (call : Call app) (remaining : List (Call app)) : State app :=
  if s.toolDispatches < s.config.maxToolCalls then
    if authorized s.config s.grant call && artifactAuthorized s call then
      {s with toolDispatches := s.toolDispatches + 1, phase := .tool call remaining}
    else if policy s.config call == .ask && artifactAuthorized s call then
      {s with phase := .ask call remaining}
    else {appendResult s call "not executed: policy denied" true with phase := .controlTools remaining}
  else stop s (.limit "tool dispatch ceiling exhausted")

def consumeControl (s : State app) (calls : Option (List (Call app))) (o : ControlObservation) : State app :=
  if o.cancelled then cancelCalls s (calls.getD [])
  else if o.deadlineExceeded then stop s (.limit "invocation deadline exceeded")
  else match calls with
    | none => admitModel s
    | some [] => {s with phase := .controlModel}
    | some (call :: rest) => admitTool s call rest

/-- Pure, total coalgebra. No closures are stored in State; this function reconstructs them. -/
def step (s : State app) : HarnessF app (State app) :=
  match s.phase with
  | .stopped outcome => ⟨.finish outcome, Empty.elim⟩
  | .controlModel => ⟨.control, fun r => advance (consumeControl s none r)⟩
  | .controlTools calls => ⟨.control, fun r => advance (consumeControl s (some calls) r)⟩
  | .model =>
    if 0 < s.modelAttempts && s.modelAttempts ≤ s.config.maxModelAttempts then
      ⟨.model (modelRequest s), fun r => advance (consumeModel s r)⟩
    else ⟨.finish (.failure "invalid model reservation"), Empty.elim⟩
  | .summary =>
    match s.pendingSummary with
    | some plan =>
      if 0 < s.modelAttempts && s.modelAttempts ≤ s.config.maxModelAttempts && planValid s plan then
        ⟨.model (summaryRequest s plan), fun r => advance (consumeSummary s plan r)⟩
      else ⟨.finish (.failure "invalid summary reservation or source"), Empty.elim⟩
    | none => ⟨.finish (.failure "missing summary source"), Empty.elim⟩
  | .tool call remaining =>
    if authorized s.config s.grant call && artifactAuthorized s call && 0 < s.toolDispatches && s.toolDispatches ≤ s.config.maxToolCalls then
      ⟨.tool call, fun r => advance (consumeTool s call remaining (r.map (app.render call.operation)))⟩
    else ⟨.finish (.failure "invalid tool authorization or reservation"), Empty.elim⟩
  | .ask call remaining => ⟨.ask call, fun r => advance (consumeApproval s call remaining r)⟩
  | .waiting delay => ⟨.wait delay, fun r => advance (consumeWait s r)⟩

end Harness
