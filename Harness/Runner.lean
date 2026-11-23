import Harness.Core.Recovery
import Harness.Adapter.Provider
import Harness.Adapter.JournalIO
import Harness.Adapter.ProviderIO
import Harness.Adapter.ProcessIO
import Harness.Adapter.ApprovalIO
import Harness.Adapter.EventIO
import Harness.Adapter.CLIProvider
import Harness.Adapter.ApplicationIO
import Harness.Adapter.PersistenceIO

namespace Harness.Runner
open Lean

structure Options where
  session : String
  output : EventIO.Output
  events : Bool := false
  script : Option (Array Json) := none
  /-- Invocation scheduling only; zero runs until a task outcome. -/
  yieldAfter : Nat := 0

structure Environment (app : Application := Coding.application) where
  options : Options
  startedMs : Nat
  runtime : ApplicationIO.Runtime app
  writer : JournalIO.Writer
  toolStartedMs : Option Nat := none

def journalPath (o : Options) : String := o.session ++ "/journal.jsonl"
/-- Cancellation targets a particular user turn. Keeping old markers avoids
erasing a concurrent cancellation while a follow-up is being admitted. -/
def cancelPath (o : Options) (turn : Nat := 0) : String :=
  o.session ++ (if turn == 0 then "/cancel" else s!"/cancel.{turn}")

abbrev canonicalSessionPath := ApplicationIO.canonicalSessionPath
abbrev validateSessionWorkspace := ApplicationIO.validateSessionWorkspace

variable {app : Application}

private def batchTools (s : State app) : List String :=
  match s.phase with
  | .tool call remaining => (call :: remaining).map fun queued => app.name queued.operation
  | _ => []

def emit (o : Options) (s : State app) (kind : String) (data : Json) : IO Unit := do
  if o.events then
    let phase := match s.phase with
      | .controlModel => "controlModel" | .model => "model" | .summary => "summary"
      | .controlTools _ => "controlTools" | .ask .. => "ask" | .tool .. => "tool"
      | .waiting _ => "waiting" | .stopped _ => "stopped"
    let payload := if data.compress.utf8ByteSize ≤ 32768 then data else
      Json.mkObj [("omitted", toJson true), ("reason", toJson "event payload exceeds 32768 bytes; inspect the journal")]
    EventIO.line o.output.stdout <| (Json.mkObj [("session", toJson s.sessionId), ("turn", toJson s.turn),
      ("operation", toJson s.nextId), ("phase", toJson phase),
      ("event", toJson kind), ("data", payload), ("outputLossIncidents", toJson (← EventIO.dropped o.output))]).compress
  else
    EventIO.humanLine o.output.stderr s!"[{s.nextId}] {kind}"

def control (env : Environment app) (s : State app) : IO ControlObservation := do
  let cancelled ← ProcessIO.cancelled (cancelPath env.options s.turn)
  let now ← IO.monoMsNow
  return {
    cancelled,
    deadlineExceeded := now - env.startedMs ≥ s.config.maxElapsedMs, monotonicMs := now}

def interrupted (env : Environment app) (s : State app) : IO Bool := do
  let c ← control env s
  return c.cancelled || c.deadlineExceeded

private def waitLoop (env : Environment app) (s : State app) : Nat → IO WaitObservation
  | 0 => return if ← interrupted env s then .interrupted else .elapsed
  | n + 1 => do
    if ← interrupted env s then return .interrupted
    IO.sleep 25
    waitLoop env s n

/-- Interpret one selected action. Decisions about retry, permission and budgets remain in step. -/
def interpret (env : Environment app) (s : State app) : (a : Action app) → IO (Reply a)
  | .control => control env s
  | .model request => do
    if ← interrupted env s then return .interrupted
    if let some responses := env.options.script then
      match responses[s.modelAttempts - 1]? with
      | some response => return Provider.normalizeResponse response
      | none => return .failure .invalidRequest "script exhausted"
    let now ← IO.monoMsNow
    let timeout := min s.config.operationTimeoutMs (s.config.maxElapsedMs - (now - env.startedMs))
    if s.config.modelBackend != .anthropic then
      return ← CLIProvider.request s.config.modelBackend request timeout
        (some (env.startedMs + s.config.maxElapsedMs)) (cancelPath env.options s.turn)
        s.config.maxResponseBytes s.config.workspace env.options.session
    ProviderIO.request request {
      endpoint := if s.config.testEndpoint.isEmpty then ProviderIO.anthropicEndpoint else s.config.testEndpoint
      timeoutMs := timeout
      invocationDeadlineMs := some (env.startedMs + s.config.maxElapsedMs)
      responseBytes := s.config.maxResponseBytes
      cancelPath := cancelPath env.options s.turn} fun text => do
        if env.options.events then
          emit env.options s "model_progress" (Json.mkObj [("provisional", toJson true), ("text", toJson text)])
        else EventIO.human env.options.output.stderr text
  | .tool call => do
    if ← interrupted env s then return .interrupted "cancelled or deadline expired before dispatch"
    let now ← IO.monoMsNow
    let remaining := s.config.maxElapsedMs - (now - env.startedMs)
    let operationRemaining := s.config.operationTimeoutMs - (now - env.toolStartedMs.getD now)
    if operationRemaining == 0 then return .failure "operation limit reached during preparation; tool was not dispatched"
    let timeout := min operationRemaining remaining
    try
      let context : ToolContext := {
        sessionPath := env.options.session
        sessionId := s.sessionId
        operationId := s.nextId
        batchTools := batchTools s
        workspace := s.config.workspace
        timeoutMs := timeout
        invocationDeadlineMs := some (env.startedMs + s.config.maxElapsedMs)
        localDeadline := operationRemaining < remaining
        outputBytes := s.config.maxToolOutputBytes
        artifactDir := env.options.session ++ "/artifacts"
        cancelPath := cancelPath env.options s.turn
        executionProfile := s.config.executionProfile
        toolchainRoots := s.config.toolchainRoots
        maxArtifactBytes := s.config.maxArtifactBytes
        maxSessionArtifactBytes := s.config.maxSessionArtifactBytes
        artifacts := s.artifacts}
      let result ← env.runtime.execute s.config context call
      match result with
      | .timedOut partialResult =>
        if ← interrupted env s then
          return .interrupted "cancelled or invocation deadline expired while settling tool timeout" partialResult
        return result
      | _ => return result
    catch _ => return .uncertain "tool IO failed; side effects may have occurred"
  | .ask call => do
    if ← interrupted env s then return .interrupted
    let droppedBefore ← EventIO.dropped env.options.output
    EventIO.line env.options.output.stderr "Approve this one operation?"
    EventIO.line env.options.output.stderr <| EventIO.approvalJSON <| Json.mkObj [
      ("application", toJson app.id), ("applicationVersion", toJson app.version),
      ("workspace", toJson s.config.workspace), ("profile", toJson s.config.executionProfile),
      ("tool", toJson (app.name call.operation)), ("arguments", app.args call.operation)]
    EventIO.write env.options.output.stderr "Type yes to approve: "
    let delivered ← EventIO.flushPending env.options.output
    unless delivered && (← EventIO.dropped env.options.output) == droppedBefore do return .interrupted
    let now ← IO.monoMsNow
    let timeout := min s.config.operationTimeoutMs (s.config.maxElapsedMs - (now - env.startedMs))
    let r ← ApprovalIO.ask timeout (cancelPath env.options s.turn)
    if ← interrupted env s then return .interrupted
    return r
  | .wait ms => waitLoop env s ((ms + 24) / 25)
  | .finish _ => throw <| IO.userError "finish has no observation"

private def interpretPrepared (env : Environment app) (s : State app) (preparationFailure : Option String) :
    (action : Action app) → IO (Reply action)
  | .tool call => match preparationFailure with
    | some message => pure (.failure message)
    | none => interpret env s (.tool call)
  | action => interpret env s action

def outcomeCode : Outcome → UInt32
  | .final _ => 0
  | .cancelled => 130
  | .limit _ => 3
  | .recoveryRequired _ => 4
  | .failure _ => 1

def reportOutcome (o : Options) (s : State app) (outcome : Outcome) : IO UInt32 := do
  emit o s "finished" (toJson outcome)
  unless o.events do
    match outcome with
    | .final answer => EventIO.document o.output (EventIO.terminalText answer)
    | other => EventIO.line o.output.stderr (toJson other).compress
  return outcomeCode outcome

/-- Only the runner is partial: each pure step terminates, while an interactive session may not. -/
partial def loop (env : Environment app) (s : State app) (completed : Nat := 0) : IO UInt32 := do
  let node := step s
  match node.1 with
  | .finish outcome =>
    try
      let _ ← PersistenceIO.commit env.writer (Json.mkObj [
        ("kind", toJson "terminal"), ("id", toJson s.nextId), ("outcome", toJson outcome)]) outcome
    catch e =>
      EventIO.line env.options.output.stderr s!"task outcome (NOT durably saved): {(toJson outcome).compress}"
      throw e
    reportOutcome env.options s outcome
  | _ =>
    if env.options.yieldAfter > 0 && completed ≥ env.options.yieldAfter then
      emit env.options s "suspended" (Json.mkObj [("durableCompletions", toJson completed)])
      return 75
    let preparingAt ← IO.monoMsNow
    let operationEnv := {env with toolStartedMs := some preparingAt}
    let (witness, preparationFailure) ← match node.1 with
      | .tool call => do
        try
          let witness ← env.runtime.prepare s.config
            {session := env.options.session, sessionId := s.sessionId, operationId := s.nextId,
              batchTools := batchTools s, startedMs := preparingAt,
              timeoutMs := min s.config.operationTimeoutMs (s.config.maxElapsedMs - (preparingAt - env.startedMs)),
              invocationDeadlineMs := some (env.startedMs + s.config.maxElapsedMs),
              cancelPath := cancelPath env.options s.turn} call
          let decoded : Option app.Witness ← IO.ofExcept <| fromJson? (toJson witness)
          unless toJson decoded == toJson witness do
            throw <| IO.userError "application witness cannot be serialized losslessly"
          if let some evidence := decoded then IO.ofExcept <| app.validateWitness call.operation evidence
          pure (decoded, none)
        catch error => pure (none, some s!"application preparation failed: {error}")
      | _ => pure (none, none)
    let operation : Persistence.Operation app := {id := s.nextId, action := node.1, witness}
    let savedReply ← PersistenceIO.operation env.writer operation
      (interpretPrepared operationEnv s preparationFailure node.1) (emit env.options s)
    loop env (node.2 savedReply) (completed + 1)

/-- Bind sessions to the executable, including its statically linked native bindings. -/
def implementationIdentity : IO String := do
  let exe ← IO.appPath
  Native.sha256 (← IO.FS.readBinFile exe)

def withLock (o : Options) (action : IO α) : IO α := do
  let session ← canonicalSessionPath o.session
  Native.withFD (Native.openDir session) fun dir =>
    Native.withFD (Native.openWriteAt dir "lock" false true 384) fun fd => do
      unless ← Native.flock fd true true do throw <| IO.userError "session is already held by another process"
      action

def start (runtime : ApplicationIO.Runtime app) (o : Options) (config : Config) (task : String) : IO UInt32 := do
  IO.ofExcept <| Capability.validate config.capabilityPolicy
  let session ← canonicalSessionPath o.session
  let o := {o with session}
  let config ← runtime.prepareConfig config
  IO.ofExcept <| Capability.validate config.capabilityPolicy
  runtime.validate session config
  JournalIO.createSession o.session
  withLock o do
    JournalIO.withWriter (journalPath o) fun writer _ => do
      runtime.initializeSession o.session config
      let identity ← implementationIdentity
      let initial ← PersistenceIO.commit writer (Json.mkObj [
        ("kind", toJson "initial"), ("schema", toJson sessionSchemaVersion),
        ("application", toJson app.id), ("applicationVersion", toJson app.version),
        ("implementation", toJson identity), ("session", toJson o.session),
        ("config", toJson config), ("task", toJson task), ("script", toJson o.script)])
        (init o.session config task app)
      loop {options := o, startedMs := ← IO.monoMsNow, runtime, writer} initial

structure Loaded (app : Application := Coding.application) where
  cursor : Recovery.Cursor app
  options : Options
  interruptedStorage : Bool
  journalCursor : Journal.Cursor := {}

/-- Offline inspection/replay only needs the journal. Resume requests workspace
validation explicitly before it can advance or dispatch another operation. -/
private def loadRecords (app : Application) (o : Options) (raw : JournalIO.ReadResult)
    (requireSessionIdentity : Bool := false) : IO (Loaded app) := do
  let sessionPath ← canonicalSessionPath o.session
  let o := {o with session := sessionPath}
  let records := raw.records
  let some initial := records[0]? | throw <| IO.userError "empty journal"
  unless (initial.getObjValAs? Nat "schema").toOption == some sessionSchemaVersion do
    throw <| IO.userError "unsupported journal schema"
  unless (initial.getObjValAs? String "kind").toOption == some "initial" do
    throw <| IO.userError "missing initial record"
  unless (initial.getObjValAs? String "application").toOption == some app.id &&
      (initial.getObjValAs? Nat "applicationVersion").toOption == some app.version do
    throw <| IO.userError "session application identity or version differs"
  let identity ← implementationIdentity
  unless (initial.getObjValAs? String "implementation").toOption == some identity do
    throw <| IO.userError "session requires the identical executable"
  let config : Config ← IO.ofExcept (initial.getObjValAs? Config "config")
  IO.ofExcept <| Capability.validate config.capabilityPolicy
  let task ← IO.ofExcept (initial.getObjValAs? String "task")
  let session ← IO.ofExcept (initial.getObjValAs? String "session")
  if requireSessionIdentity && session != sessionPath then
    throw <| IO.userError "saved session identity differs from its canonical directory; relocated sessions cannot resume"
  let script ← IO.ofExcept (initial.getObjValAs? (Option (Array Json)) "script")
  let cursor ← IO.ofExcept <| Recovery.replay (init session config task app) (records.toList.drop 1)
  return {
    cursor, options := {o with script},
    interruptedStorage := raw.interrupted, journalCursor := raw.cursor}

def load (app : Application) (o : Options) (requireSessionIdentity : Bool := false) : IO (Loaded app) := do
  let raw ← JournalIO.read (journalPath o)
  loadRecords app o raw requireSessionIdentity

def inspect (app : Application) (o : Options) : IO UInt32 := withLock o do
  let loaded ← load app o
  EventIO.document o.output <| (Json.mkObj [("state", toJson loaded.cursor.state),
    ("application", toJson app.id), ("applicationVersion", toJson app.version),
    ("openedSession", toJson loaded.options.session),
    ("pending", toJson loaded.cursor.pending), ("terminal", toJson loaded.cursor.terminal),
    ("recoverableOperation", toJson ((Recovery.target loaded.cursor).map (·.nextId))),
    ("editWitness", toJson loaded.cursor.editWitness),
    ("journal", toJson loaded.journalCursor),
    ("interruptedStorage", toJson loaded.interruptedStorage)]).pretty
  return 0

private def persistResolution (writer : JournalIO.Writer) (o : Options) (cursor : Recovery.Cursor app) (id : Nat)
    (resolution : app.Resolution) : IO (Recovery.Cursor app) := do
  let encoded := toJson resolution
  let resolution : app.Resolution ← IO.ofExcept <| fromJson? encoded
  unless toJson resolution == encoded do
    throw <| IO.userError "application resolution cannot be serialized losslessly"
  let next ← IO.ofExcept <| Recovery.resolve cursor id resolution
  let operator := app.operatorResolution resolution
  let next ← PersistenceIO.commit writer (Json.mkObj [("kind", toJson "resolution"),
    ("id", toJson id), ("resolution", toJson resolution),
    ("source", toJson (if operator then "operator" else "application_evidence")),
    ("resourcesSettled", toJson operator)]) next
  emit o cursor.state "resolution" (toJson resolution)
  return next

private def persistRecovery (writer : JournalIO.Writer) (o : Options) (cursor : Recovery.Cursor app) (id : Nat)
    (disposition : Recovery.Disposition) : IO (Recovery.Cursor app) := do
  let next ← IO.ofExcept <| Recovery.recover cursor id disposition
  let next ← PersistenceIO.commit writer (Recovery.recoveryRecord id disposition) next
  emit o cursor.state "recovery" (toJson disposition)
  return next

/-- Reconcile desired contents, without claiming that the original effect ran
exactly once. A preimage or conflict remains unresolved and is never replayed. -/
private def reconcile (runtime : ApplicationIO.Runtime app) (writer : JournalIO.Writer) (o : Options)
    (cursor : Recovery.Cursor app) : IO (Recovery.Cursor app) := do
  let some prior := Recovery.target cursor | return cursor
  match (step prior).1 with
  | .tool call =>
    let resolution ← runtime.reconcile prior.config
      {session := o.session, sessionId := prior.sessionId, operationId := prior.nextId} call cursor.editWitness
    unless !app.operatorResolution resolution do
      throw <| IO.userError "automatic reconciliation cannot assert an operator decision"
    persistResolution writer o cursor prior.nextId resolution
  | _ => throw <| IO.userError "unresolved operation has no application reconciliation"

/-- An operator supplies provenance for an uncertain process. This writes no
task files, executes no command, and does not infer independent task success. -/
def resolveOperation (runtime : ApplicationIO.Runtime app) (o : Options) (id : Nat)
    (resolution : app.Resolution) (resourcesSettled : Bool)
    (abandonNote : Option String := none) : IO UInt32 := withLock o do
  JournalIO.withWriter (journalPath o) fun writer raw => do
    let loaded ← loadRecords app o raw true
    runtime.validateIdentity loaded.options.session loaded.cursor.state.config
    unless app.operatorResolution resolution do
      throw <| IO.userError "application evidence reconciliation is performed by resume"
    let prior ← IO.ofExcept <| Recovery.checkedTarget loaded.cursor
    let next ← match (step prior).1, abandonNote with
      | .tool call, some note =>
        if app.mayAbandon call.operation then
          persistRecovery writer loaded.options loaded.cursor id (.mutationAbandoned note)
        else resolveWithResources writer loaded.options loaded.cursor
      | _, _ => resolveWithResources writer loaded.options loaded.cursor
    unless o.events do
      EventIO.document o.output s!"Recorded operator resolution for operation {id}; no operation was executed. Use resume to continue."
    return if (Recovery.target next).isNone then 0 else 4
where
  resolveWithResources (writer : JournalIO.Writer) (options : Options) (cursor : Recovery.Cursor app) : IO (Recovery.Cursor app) := do
    unless resourcesSettled do
      throw <| IO.userError "process resolution requires --resources-settled: confirm the original process and descendants can no longer act"
    persistResolution writer options cursor id resolution

def resume (runtime : ApplicationIO.Runtime app) (o : Options) : IO UInt32 := withLock o do
  JournalIO.withWriter (journalPath o) fun writer raw => do
    let loaded ← loadRecords app o raw true
    let config := loaded.cursor.state.config
    runtime.validate loaded.options.session config
    let cursor ← match Recovery.automaticRecovery? loaded.cursor with
      | some disposition =>
        let prior ← IO.ofExcept <| Recovery.checkedTarget loaded.cursor
        persistRecovery writer loaded.options loaded.cursor prior.nextId disposition
      | none =>
        if (Recovery.target loaded.cursor).isSome then reconcile runtime writer loaded.options loaded.cursor
        else pure loaded.cursor
    if cursor.terminal then
      match (step cursor.state).1 with
      | .finish outcome => reportOutcome o cursor.state outcome
      | _ => throw <| IO.userError "invalid terminal state"
    else
      loop {options := loaded.options, startedMs := ← IO.monoMsNow, runtime, writer} cursor.state

/-- A trusted user starts another turn only at a settled durable boundary.
Prior cancellation markers retain their original turn identity. -/
def continueSession (runtime : ApplicationIO.Runtime app) (o : Options) (task : String) : IO UInt32 := withLock o do
  JournalIO.withWriter (journalPath o) fun writer raw => do
    let loaded ← loadRecords app o raw true
    runtime.validate loaded.options.session loaded.cursor.state.config
    let previous := loaded.cursor.state
    let accepted ← IO.ofExcept <| Recovery.newTurn loaded.cursor previous.nextId (previous.turn + 1) task
    let accepted ← PersistenceIO.commit writer
      (Recovery.userTurnRecord previous.nextId (previous.turn + 1) task) accepted
    emit loaded.options accepted.state "user_turn" (Json.mkObj [("task", toJson task)])
    loop {options := loaded.options, startedMs := ← IO.monoMsNow, runtime, writer} accepted.state

/-- Read a validated visible journal prefix without taking the execution lock,
then cancel that observed turn. The reported identity makes a race with admission
explicit; a subsequent turn does not erase or inherit this request. -/
def cancel (app : Application) (o : Options) : IO UInt32 := do
  let loaded ← load app o true
  let turn := loaded.cursor.state.turn
  let name := if turn == 0 then "cancel" else s!"cancel.{turn}"
  Native.withFD (Native.openDir loaded.options.session) fun dir => do
    Native.withFD (Native.openWriteAt dir name false true 384) fun fd => do
      Native.write fd "cancel\n".toUTF8
      Native.sync fd
    Native.sync dir
  emit o loaded.cursor.state "cancellation_requested" (Json.mkObj [("targetTurn", toJson turn)])
  return 0

/-- Resolve only a statically installed identity. The selected loader repeats
these checks under the session lock before it decodes or executes any app call. -/
def savedApplication (o : Options) : IO (String × Nat) := do
  let raw ← JournalIO.read (journalPath o)
  let some initial := raw.records[0]? | throw <| IO.userError "empty journal"
  unless (initial.getObjValAs? Nat "schema").toOption == some sessionSchemaVersion &&
      (initial.getObjValAs? String "kind").toOption == some "initial" do
    throw <| IO.userError "unsupported journal schema or initial record"
  return (← IO.ofExcept (initial.getObjValAs? String "application"),
    ← IO.ofExcept (initial.getObjValAs? Nat "applicationVersion"))

end Harness.Runner
