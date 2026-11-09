import Harness.Core.Effects
import Harness.Core.ModelResponse

/-!
# Pure Transition Function

`step` is a total coalgebra `State → HarnessF State` over the concrete `CodingAPI`. It emits the
next `Action` together with a continuation that consumes its typed reply. The core performs no
IO; adapters execute effects elsewhere.

The `consume*` functions interpret model, summary, tool, approval, wait and control
observations. `admitTask`, `admitSummary`, `admitModel` and `admitTool` reserve attempt and
dispatch budgets, check context admission and authorization, and choose compaction. `advance`
increments `nextId` after every consumed observation.
-/

namespace Harness
open Lean

/-- Each consumed observation advances the serializable operation identity. -/
def advance (s : State) : State := { s with nextId := s.nextId + 1 }

def appendResult (s : State) (call : ToolCall) (text : String) (isError : Bool) : State :=
  let block := Json.mkObj [("type", toJson "tool_result"), ("tool_use_id", toJson call.id),
    ("content", toJson text), ("is_error", toJson isError)]
  let history := match s.history.reverse with
    | last :: rest => if last.role == "user" then
        ( {last with content := last.content.push block} :: rest).reverse
      else s.history ++ [{role := "user", content := #[block]}]
    | [] => [{role := "user", content := #[block]}]
  {s with history, grant := none}

def accountUsage (s : State) (usage : Option Usage) : State :=
  match usage with
  | some u => {s with knownInputTokens := s.knownInputTokens + u.inputTokens, knownOutputTokens := s.knownOutputTokens + u.outputTokens}
  | none => {s with unknownUsage := s.unknownUsage + 1}

def retryOrStop (s : State) (message : String) : State :=
  if s.retryCount < s.config.maxRetries && s.modelAttempts < s.config.maxModelAttempts then
    {s with retryCount := s.retryCount + 1, phase := .waiting (1000 * (s.retryCount + 1))}
  else stop s (.failure message)

def consumeModel (s : State) : ModelObservation → State
  | .interrupted => stop {s with unknownUsage := s.unknownUsage + 1} .cancelled
  | .uncertain message => retryOrStop {s with unknownUsage := s.unknownUsage + 1} message
  | .failure kind message =>
    let s := {s with unknownUsage := s.unknownUsage + 1}
    match kind with
    | .rateLimit => retryOrStop s message
    | .transport => retryOrStop s message
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
        match validateBatch s.config s.seenCallIds response.calls with
        | .error message => stop s (.failure s!"invalid tool batch: {message}")
        | .ok calls =>
          {s with history := s.history ++ [{role := "assistant", content := response.content}], phase := .controlTools calls, seenCallIds := s.seenCallIds ++ calls.map (·.id), retryCount := 0, grant := none}
    | .contextOverflow => stop s (.limit "provider context allowance exceeded")
    | .maxTokens => stop s (.failure "model output truncated; no tool calls executed")
    | .refusal => stop s (.failure "model refusal")
    | .other => stop s (.failure "unsupported model stop reason")

/-- The proposed active view, retaining its source metadata and complete response. -/
def summaryCandidate (s : State) (plan : SummaryPlan) (response : ModelResponse) : State :=
  {s with activeView := some (summaryView plan response), pendingSummary := none, summaries := s.summaries ++ [{plan, response}], phase := .controlModel, retryCount := 0, grant := none}

/-- A summary becomes an active view only after complete response validation and
admission of the reconstructed next task request. Raw history is untouched. -/
def installSummary (s : State) (plan : SummaryPlan) (response : ModelResponse) : State :=
  let candidate := summaryCandidate s plan response
  if contextAdmitted candidate && historyValid (activeMessages candidate) then candidate
  else stop s (.limit "compacted context exceeds allowance or has invalid tool pairing")

def consumeSummary (s : State) (plan : SummaryPlan) : ModelObservation → State
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

def consumeTool (s : State) (call : ToolCall) (remaining : List ToolCall) : ToolObservation ToolResult → State
  | .success r =>
    let error := match r.exitCode with | some n => n != 0 | none => false
    {appendResult s call (toJson r).compress error with phase := .controlTools remaining}
  | .failure message => {appendResult s call message true with phase := .controlTools remaining}
  | .interrupted message => stop s (.recoveryRequired s!"tool interrupted; effects may be partial: {message}")
  | .uncertain message => stop s (.recoveryRequired message)

def consumeApproval (s : State) (call : ToolCall) (remaining : List ToolCall) : ApprovalObservation → State
  | .approved => {s with grant := some call, phase := .controlTools (call :: remaining)}
  | .denied => {appendResult s call "not executed: approval denied" true with phase := .controlTools remaining}
  | .interrupted => stop s .cancelled

def consumeWait (s : State) : WaitObservation → State
  | .elapsed => {s with phase := .controlModel}
  | .interrupted => stop s .cancelled

/-- Reservation is part of the explicit state before the task action is emitted. -/
def admitTask (s : State) : State :=
  if s.modelAttempts < s.config.maxModelAttempts then
    if contextAdmitted s then
      if historyValid (activeMessages s) then
        {s with modelAttempts := s.modelAttempts + 1, phase := .model}
      else stop s (.failure "active context has invalid tool pairing")
    else stop s (.limit "context allowance exhausted")
  else stop s (.limit "model attempt ceiling exhausted")

def admitSummary (s : State) (plan : SummaryPlan) : State :=
  if s.modelAttempts < s.config.maxModelAttempts then
    if planValid s plan then
      {s with modelAttempts := s.modelAttempts + 1, phase := .summary, pendingSummary := some plan, grant := none}
    else stop s (.limit "no admissible compaction source and suffix")
  else stop s (.limit "model attempt ceiling exhausted")

/-- Called only at the boundary after a complete tool batch in reachable states.
Retries retain their exact pending summary source; no summary runs amid a batch. -/
def admitModel (s : State) : State :=
  match s.pendingSummary with
  | some plan => admitSummary s plan
  | none =>
    if wantsCompaction s then
      match planCompaction s with
      | some plan => admitSummary s plan
      | none => admitTask s
    else admitTask s

/-- A successful grant is consumed by exactly this operation; it is never reused. -/
def admitTool (s : State) (call : ToolCall) (remaining : List ToolCall) : State :=
  if s.toolDispatches < s.config.maxToolCalls then
    if authorized s.config s.grant call then
      {s with toolDispatches := s.toolDispatches + 1, phase := .tool call remaining}
    else if policy s.config call == .ask then
      {s with phase := .ask call remaining}
    else {appendResult s call "not executed: policy denied" true with phase := .controlTools remaining}
  else stop s (.limit "tool dispatch ceiling exhausted")

def consumeControl (s : State) (calls : Option (List ToolCall)) (o : ControlObservation) : State :=
  if o.cancelled then stop s .cancelled
  else if o.deadlineExceeded then stop s (.limit "invocation deadline exceeded")
  else match calls with
    | none => admitModel s
    | some [] => {s with phase := .controlModel}
    | some (call :: rest) => admitTool s call rest

/-- Pure, total coalgebra. No closures are stored in State; this function reconstructs them. -/
def step (s : State) : HarnessF State :=
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
    if authorized s.config s.grant call && 0 < s.toolDispatches && s.toolDispatches ≤ s.config.maxToolCalls then
      ⟨.tool call, fun r => advance (consumeTool s call remaining r)⟩
    else ⟨.finish (.failure "invalid tool authorization or reservation"), Empty.elim⟩
  | .ask call remaining => ⟨.ask call, fun r => advance (consumeApproval s call remaining r)⟩
  | .waiting delay => ⟨.wait delay, fun r => advance (consumeWait s r)⟩

end Harness
