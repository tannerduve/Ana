import Harness.Core.Effects
import Harness.Core.ModelResponse

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

/-- Reservation is part of the explicit state before the model action is emitted. -/
def admitModel (s : State) : State :=
  if s.modelAttempts < s.config.maxModelAttempts then
    if contextAdmitted s then
      {s with modelAttempts := s.modelAttempts + 1, phase := .model}
    else stop s (.limit "context allowance exhausted")
  else stop s (.limit "model attempt ceiling exhausted")

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
  | .stopped outcome => Sigma.mk (.finish outcome) Empty.elim
  | .controlModel => Sigma.mk .control (fun r => advance (consumeControl s none r))
  | .controlTools calls => Sigma.mk .control (fun r => advance (consumeControl s (some calls) r))
  | .model =>
    if 0 < s.modelAttempts && s.modelAttempts ≤ s.config.maxModelAttempts then
      Sigma.mk (.model (modelRequest s)) (fun r => advance (consumeModel s r))
    else Sigma.mk (.finish (.failure "invalid model reservation")) Empty.elim
  | .tool call remaining =>
    if authorized s.config s.grant call && 0 < s.toolDispatches && s.toolDispatches ≤ s.config.maxToolCalls then
      Sigma.mk (.tool call) (fun r => advance (consumeTool s call remaining r))
    else Sigma.mk (.finish (.failure "invalid tool authorization or reservation")) Empty.elim
  | .ask call remaining => Sigma.mk (.ask call) (fun r => advance (consumeApproval s call remaining r))
  | .waiting delay => Sigma.mk (.wait delay) (fun r => advance (consumeWait s r))

end Harness
