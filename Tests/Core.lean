import Harness.Proofs.Invariants

def Except.isError {ε α : Type} (r : Except ε α) : Bool := !r.isOk

namespace Tests.Core
open Harness Lean

def cfg : Config := {model := "scripted", workspace := "/tmp/scripted", commands := .allow}

def raw (id name : String) (input : Json) : RawCall := ⟨id, name, input⟩
def readCall : RawCall := raw "read-1" "read" (Json.mkObj [("path", toJson "main.txt")])
def editCall : RawCall := raw "edit-1" "edit" (toJson ({path := "main.txt", old := "broken", new := "fixed", expectedSha256 := String.ofList (List.replicate 64 '0')} : EditArgs))
def processCall : RawCall := raw "test-1" "process" (Json.mkObj [("argv", toJson #["test"])] )

def callBlock (call : RawCall) : Json :=
  Json.mkObj [("type", toJson "tool_use"), ("id", toJson call.id),
    ("name", toJson call.name), ("input", call.input)]

def toolResponse (call : RawCall) : ModelObservation := .success {
  content := #[callBlock call],
  calls := [call], text := "", stop := .toolUse }

def finalResponse : ModelObservation := .success {
  content := #[textBlock "Fixed the file; tests passed."], calls := [],
  text := "Fixed the file; tests passed.", stop := .endTurn }

/-- A bounded scripted interpreter executes the same dependent continuations as IO. -/
def scripted : Nat → State → List ModelObservation → String → Except String (State × String)
  | 0, _, _, _ => .error "script fuel exhausted"
  | n+1, s, models, file =>
    match step s with
    | ⟨.finish _, _⟩ => .ok (s, file)
    | ⟨.control, k⟩ => scripted n (k {}) models file
    | ⟨.model _, k⟩ => match models with
      | [] => .error "script has no model response"
      | r :: rest => scripted n (k r) rest file
    | ⟨.tool call, k⟩ => match call.operation with
      | .readFile _ => scripted n (k (.success {text := file})) models file
      | .editFile a =>
        if file == a.old then scripted n (k (.success {text := "edited"})) models a.new
        else .error "script preimage mismatch"
      | .runProcess _ =>
        if file == "fixed" then scripted n (k (.success {text := "tests passed", exitCode := some 0})) models file
        else .error "script tests failed"
      | _ => .error "unexpected scripted tool"
    | ⟨.ask _, k⟩ => scripted n (k .denied) models file
    | ⟨.wait _, k⟩ => scripted n (k .elapsed) models file

def expect (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def isFailure (s : State) : Bool := match s.phase with | .stopped (.failure _) => true | _ => false
def isLimit (s : State) : Bool := match s.phase with | .stopped (.limit _) => true | _ => false

structure ObservedRun where
  state : State
  requests : List ModelRequest
  effects : List ToolCall

/-- An instrumented interpreter records actual model/tool actions emitted by step.
    A spare final response lets a faulty core continue, exposing extra dispatches. -/
def observeScript : Nat → State → List ModelObservation → List ModelRequest → List ToolCall →
    Except String ObservedRun
  | 0, _, _, _, _ => .error "observed script fuel exhausted"
  | fuel + 1, s, models, requests, effects =>
    match step s with
    | ⟨.finish _, _⟩ => .ok {state := s, requests, effects}
    | ⟨.control, k⟩ => observeScript fuel (k {}) models requests effects
    | ⟨.model request, k⟩ => match models with
      | [] => .error "unexpected additional model call"
      | observation :: rest =>
        observeScript fuel (k observation) rest (requests ++ [request]) effects
    | ⟨.tool call, k⟩ =>
      observeScript fuel (k (.success {text := s!"completed {call.id}"})) models
        requests (effects ++ [call])
    | ⟨.ask _, k⟩ => observeScript fuel (k .approved) models requests effects
    | ⟨.wait _, k⟩ => observeScript fuel (k .elapsed) models requests effects

private def secondRead : RawCall :=
  raw "read-2" "read" (Json.mkObj [("path", toJson "other.txt")])

private def measuredResponse : ModelResponse := {
  content := #[callBlock readCall], calls := [readCall], text := "", stop := .toolUse,
  usage := some {inputTokens := 17, outputTokens := 4} }

/-- These values bypass the provider decoder: typed success alone is insufficient. -/
private def inconsistentResponses : List (String × ModelResponse) := [
  ("call without content", {measuredResponse with content := #[]}),
  ("content without call", {measuredResponse with calls := []}),
  ("different call identity", {measuredResponse with
    content := #[callBlock {readCall with id := "different-id"}]}),
  ("different tool name", {measuredResponse with
    content := #[callBlock {readCall with name := "list"}]}),
  ("different arguments", {measuredResponse with
    content := #[callBlock {readCall with input := secondRead.input}]}),
  ("reordered calls", {measuredResponse with
    calls := [readCall, secondRead], content := #[callBlock secondRead, callBlock readCall]}),
  ("malformed block after first call", {measuredResponse with
    content := #[callBlock readCall, Json.mkObj [("type", toJson "text")]]}),
  ("unknown block after first call", {measuredResponse with
    content := #[callBlock readCall, Json.mkObj [("type", toJson "future_block")]]}),
  ("tool-turn text disagrees", {measuredResponse with
    content := #[textBlock "actual", callBlock readCall], text := "invented"}),
  ("final text disagrees", {measuredResponse with
    content := #[textBlock "actual"], calls := [], text := "invented", stop := .endTurn}),
  ("end-turn hides a call", {measuredResponse with calls := [], stop := .endTurn})]

private def runResponseConsistency : IO Unit := do
  let initial := init "consistency-session" cfg "inspect files"
  for (label, response) in inconsistentResponses do
    let observed ← IO.ofExcept <| observeScript 30 initial [.success response, finalResponse] [] []
    expect (isFailure observed.state) s!"{label}: inconsistent success did not fail"
    expect (observed.effects.isEmpty && observed.state.toolDispatches == 0)
      s!"{label}: rejected response dispatched a tool"
    expect (observed.requests.length == 1 && observed.state.modelAttempts == 1)
      s!"{label}: rejected response triggered inference or lost its reservation"
    expect ((toJson observed.state.history).compress == (toJson initial.history).compress &&
      observed.state.seenCallIds == initial.seenCallIds)
      s!"{label}: rejected response changed authoritative history or admitted IDs"
    expect (observed.state.knownInputTokens == 17 && observed.state.knownOutputTokens == 4 &&
      observed.state.unknownUsage == 0) s!"{label}: rejected response lost reported usage"
    expect (match (step observed.state).fst with | .finish (.failure _) => true | _ => false)
      s!"{label}: failure is not terminal"
  let missingUsage := {measuredResponse with content := #[], usage := none}
  let unknown ← IO.ofExcept <| observeScript 30 initial [.success missingUsage, finalResponse] [] []
  expect (isFailure unknown.state && unknown.effects.isEmpty && unknown.requests.length == 1 &&
    unknown.state.modelAttempts == 1 && unknown.state.unknownUsage == 1 &&
    unknown.state.knownInputTokens == 0 && unknown.state.knownOutputTokens == 0)
    "rejected response fabricated absent usage"
  let thinking := Json.mkObj [("type", toJson "thinking"), ("thinking", toJson "inspect both"),
    ("signature", toJson "opaque-signature")]
  let redacted := Json.mkObj [("type", toJson "redacted_thinking"), ("data", toJson "opaque-data")]
  let accepted : ModelResponse := {measuredResponse with
    content := #[thinking, textBlock "Inspecting both files.", callBlock readCall,
      redacted, callBlock secondRead], calls := [readCall, secondRead], text := "Inspecting both files."}
  let observed ← IO.ofExcept <| observeScript 30 initial [.success accepted, finalResponse] [] []
  expect (match observed.state.phase with | .stopped (.final _) => true | _ => false)
    "valid opaque-content batch did not finish"
  expect (observed.effects.map (·.id) == [readCall.id, secondRead.id] &&
    observed.state.toolDispatches == 2 && observed.state.modelAttempts == 2)
    "valid batch lost ordering or dispatch accounting"
  let some nextRequest := observed.requests[1]? | throw (IO.userError "valid batch lacked follow-on inference")
  let some assistant := nextRequest.messages[1]? | throw (IO.userError "missing accepted assistant content")
  expect (assistant.role == "assistant" && (toJson assistant.content).compress == (toJson accepted.content).compress)
    "accepted opaque content or signature changed before follow-on inference"
  let some results := nextRequest.messages[2]? | throw (IO.userError "missing tool results")
  let ids := results.content.toList.map fun block => (block.getObjValAs? String "tool_use_id").toOption
  expect (results.role == "user" && ids == [some readCall.id, some secondRead.id])
    "follow-on inference omitted or reordered protocol results"
  IO.println s!"core: {inconsistentResponses.length} inconsistent-response fixtures rejected; unknown-usage and valid opaque-batch checks passed"

def run : IO Unit := do
  let s := init "test-session" cfg "repair the file"
  let (done, file) ← match scripted 50 s [toolResponse readCall, toolResponse editCall,
      toolResponse processCall, finalResponse] "broken" with
    | .ok result => pure result
    | .error e => throw (IO.userError e)
  expect (file == "fixed") "script did not edit file"
  expect (done.modelAttempts == 4 && done.toolDispatches == 3) "wrong scripted reservations"
  expect (match done.phase with | .stopped (.final _) => true | _ => false) "script failed to finish"
  expect ((decodeCall readCall).isOk) "path-only read defaults failed"
  expect ((decodeCall processCall).isOk) "argv-only process defaults failed"
  expect ((decodeCall (raw "create-default" "create" (Json.mkObj [("path", toJson "x"), ("content", toJson "y")]))).isOk) "create defaults failed"
  expect ((decodeCall (raw "list-default" "list" (Json.mkObj []))).isOk) "list defaults failed"
  expect ((decodeCall (raw "search-default" "search" (Json.mkObj [("query", toJson "x")]))).isOk) "search defaults failed"
  expect ((decodeCall (raw "missing" "read" (Json.mkObj []))).isError) "required field fabricated"
  expect ((decodeCall (raw "override" "read" (Json.mkObj [("path", toJson "x"), ("startLine", toJson (0 : Nat))]))).isError) "explicit option overwritten by default"
  expect ((validateBatch cfg [] [readCall, readCall]).isError) "duplicate call accepted"
  expect ((validateBatch cfg ["read-1"] [readCall]).isError) "historical call identity reused"
  expect ((validateBatch cfg [] [readCall, raw "bad" "unknown" (Json.mkObj [])]).isError) "bad later call accepted"
  expect ((decodeCall (raw "bad" "read" (Json.mkObj [("path", toJson "../escape")]))).isError) "path escape accepted"
  expect ((decodeCall (raw "bad" "process" (Json.mkObj [("argv", toJson #["echo"]), ("env", Json.mkObj [])]))).isError) "unknown arguments stripped"
  let incomplete : ModelResponse := {content := #[], calls := [readCall], text := "", stop := .maxTokens}
  let truncated := consumeModel s (.success incomplete)
  expect ((match truncated.phase with | .controlModel => true | _ => false) && truncated.toolDispatches == 0 &&
    toJson truncated.history == toJson (s.history ++ [responseRepairMessage .truncated])) "truncated response authorized work or lost bounded feedback"
  let malformed := consumeModel s (.success {incomplete with stop := .toolUse, calls := [readCall, readCall]})
  expect (isFailure malformed && malformed.history.length == 1) "malformed batch entered history"
  expect (isLimit (admitModel {s with config := {cfg with maxContextBytes := 1}})) "context exhaustion ignored"
  expect (isLimit (admitModel {s with modelAttempts := cfg.maxModelAttempts})) "model budget exhausted incorrectly"
  let cancelled := consumeControl s none {cancelled := true}
  expect (match (step cancelled).fst with | .finish .cancelled => true | _ => false) "cancellation not terminal"
  let command : ToolCall := ⟨"cmd", .runProcess {argv := #["echo", "hello"]}⟩
  let changed : ToolCall := {command with operation := .runProcess {argv := #["echo", "different"]}}
  let askCfg := {cfg with commands := .ask}
  expect (authorized askCfg (some command) command) "exact grant rejected"
  expect (!authorized askCfg (some command) changed) "changed grant accepted"
  let denied := admitTool {s with config := {cfg with commands := .deny}} command []
  expect (denied.toolDispatches == 0) "denied command consumed dispatch"
  let interrupted := consumeTool s command [] (.interrupted "killed")
  expect (match interrupted.phase with | .stopped (.recoveryRequired _) => true | _ => false) "uncertain mutation flattened"
  let retry := consumeModel {s with modelAttempts := 1} (.failure .rateLimit "429")
  expect (retry.retryCount == 1 && retry.modelAttempts == 1 && retry.unknownUsage == 1) "retry accounting incorrect"
  let exhausted := consumeModel {s with retryCount := cfg.maxRetries} (.failure .transport "lost")
  expect (isFailure exhausted) "retry limit ignored"
  let roundTrip : Except String State := fromJson? (toJson done)
  expect (match roundTrip with | .ok restored => (toJson restored).compress == (toJson done).compress | .error _ => false) "state roundtrip failed"
  expect (match replyFromJson (app := Coding.application) (.finish (.final "done")) Json.null with | .error _ => true | .ok _ => false) "manufactured terminal reply"
  runResponseConsistency
  IO.println "core: scripted read/edit/test, validation, policy, limits, retry, serialization checks passed"

end Tests.Core
