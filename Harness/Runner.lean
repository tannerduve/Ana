import Harness.Core.Recovery
import Harness.Adapter.Provider
import Harness.Adapter.JournalIO
import Harness.Adapter.ProviderIO
import Harness.Adapter.ProcessIO
import Harness.Adapter.ApprovalIO

namespace Harness.Runner
open Lean

structure Options where
  session : String
  events : Bool := false
  script : Option (Array Json) := none

structure Environment where
  options : Options
  startedMs : Nat

def journalPath (o : Options) : String := o.session ++ "/journal.jsonl"
def cancelPath (o : Options) : String := o.session ++ "/cancel"

private def resolveProspective (base : System.FilePath) : List String → IO System.FilePath
  | [] => pure base
  | "." :: rest => resolveProspective base rest
  | ".." :: rest => resolveProspective (base.parent.getD "/") rest
  | part :: rest => do
    let candidate := base / part
    let present ← try
        let _ ← candidate.symlinkMetadata
        pure true
      catch
        | .noFileOrDirectory .. => pure false
        | error => throw error
    let resolved ← if present then IO.FS.realPath candidate else pure candidate
    if present then
      unless (← resolved.metadata).type == .dir do
        throw <| IO.userError "session path contains a non-directory component"
    resolveProspective resolved rest

/-- Resolve existing ancestors before interpreting the missing suffix. This avoids
lexically normalizing `symlink/..` against the wrong directory. Trusted session
ancestors must not be renamed concurrently with validation/creation. -/
def canonicalSessionPath (path : String) : IO String := do
  if path.isEmpty || path.contains '\x00' then
    throw <| IO.userError "session path must be nonempty and contain no NUL"
  let path := System.FilePath.mk path
  let absolute ← if path.isAbsolute then pure path else do
    let current ← IO.currentDir
    pure (current / path)
  let parts := absolute.components.filter (fun part => !part.isEmpty)
  if parts.length > 256 then throw <| IO.userError "session directory nesting limit exceeded"
  return (← resolveProspective "/" parts).toString

/-- Keep trusted session state outside direct-file tool authority. Both containment
directions are rejected using canonical path components, including parent aliases.
This does not isolate an approved general process running as the same OS user. -/
def validateSessionWorkspace (session workspace : String) : IO (String × String) := do
  if workspace.isEmpty || workspace.contains '\x00' then
    throw <| IO.userError "workspace path must be nonempty and contain no NUL"
  let workspace ← IO.FS.realPath workspace
  unless (← workspace.metadata).type == .dir do
    throw <| IO.userError "workspace must be a directory"
  let session ← canonicalSessionPath session
  let sessionParts := (System.FilePath.mk session).components.filter (fun part => !part.isEmpty)
  let workspaceParts := workspace.components.filter (fun part => !part.isEmpty)
  if sessionParts.isPrefixOf workspaceParts || workspaceParts.isPrefixOf sessionParts then
    throw <| IO.userError "session and workspace must not overlap; choose session storage outside the workspace"
  return (session, workspace.toString)

def emit (o : Options) (s : State) (kind : String) (data : Json) : IO Unit := do
  if o.events then
    IO.println <| (Json.mkObj [("session", toJson s.sessionId), ("turn", toJson (0 : Nat)),
      ("operation", toJson s.nextId), ("phase", toJson s.phase),
      ("event", toJson kind), ("data", data)]).compress
  else
    (← IO.getStderr).putStrLn s!"[{s.nextId}] {kind}"

def control (env : Environment) (s : State) : IO ControlObservation := do
  let now ← IO.monoMsNow
  return {
    cancelled := (← ProcessIO.cancelled (cancelPath env.options)),
    deadlineExceeded := now - env.startedMs ≥ s.config.maxElapsedMs, monotonicMs := now}

def interrupted (env : Environment) (s : State) : IO Bool := do
  let c ← control env s
  return c.cancelled || c.deadlineExceeded

private def waitLoop (env : Environment) (s : State) : Nat → IO WaitObservation
  | 0 => return if ← interrupted env s then .interrupted else .elapsed
  | n + 1 => do
    if ← interrupted env s then return .interrupted
    IO.sleep 25
    waitLoop env s n

/-- Interpret one selected action. Decisions about retry, permission and budgets remain in step. -/
def interpret (env : Environment) (s : State) : (a : Action) → IO (Reply a)
  | .control => control env s
  | .model request => do
    if ← interrupted env s then return .interrupted
    if let some responses := env.options.script then
      match responses[s.modelAttempts - 1]? with
      | some response => return Provider.normalizeResponse response
      | none => return .failure .invalidRequest "script exhausted"
    let now ← IO.monoMsNow
    let timeout := min s.config.operationTimeoutMs (s.config.maxElapsedMs - (now - env.startedMs))
    ProviderIO.request request {
      timeoutMs := timeout
      responseBytes := s.config.maxResponseBytes
      cancelPath := cancelPath env.options}
  | .tool call => do
    if ← interrupted env s then return .interrupted "cancelled or deadline expired before dispatch"
    let now ← IO.monoMsNow
    let timeout := min s.config.operationTimeoutMs (s.config.maxElapsedMs - (now - env.startedMs))
    try
      let context : ToolContext := {
        workspace := s.config.workspace
        timeoutMs := timeout
        outputBytes := s.config.maxToolOutputBytes
        artifactDir := env.options.session ++ "/artifacts"
        cancelPath := cancelPath env.options}
      match call.operation with
      | .runProcess args => ProcessIO.run context args
      | _ => FilesystemIO.run context call
    catch _ => return .uncertain "tool IO failed; side effects may have occurred"
  | .ask call => do
    if ← interrupted env s then return .interrupted
    let err ← IO.getStderr
    err.putStrLn s!"Approve one operation in {s.config.workspace}?"
    err.putStrLn (Json.mkObj [("tool", toJson call.operation.name), ("arguments", call.operation.args)]).pretty
    err.putStr "Type yes to approve: "
    err.flush
    let now ← IO.monoMsNow
    let timeout := min s.config.operationTimeoutMs (s.config.maxElapsedMs - (now - env.startedMs))
    let r ← ApprovalIO.ask timeout (cancelPath env.options)
    if ← interrupted env s then return .interrupted
    return r
  | .wait ms => waitLoop env s ((ms + 24) / 25)
  | .finish _ => throw <| IO.userError "finish has no observation"

def outcomeCode : Outcome → UInt32
  | .final _ => 0
  | .cancelled => 130
  | .limit _ => 3
  | .recoveryRequired _ => 4
  | .failure _ => 1

def reportOutcome (o : Options) (s : State) (outcome : Outcome) : IO UInt32 := do
  emit o s "finished" (toJson outcome)
  unless o.events do
    match outcome with
    | .final answer => IO.println answer
    | other => (← IO.getStderr).putStrLn (toJson other).compress
  return outcomeCode outcome

/-- Only the runner is partial: each pure step terminates, while an interactive session may not. -/
partial def loop (env : Environment) (s : State) : IO UInt32 := do
  let node := step s
  match node.1 with
  | .finish outcome =>
    try
      JournalIO.append (journalPath env.options) <| Json.mkObj [
        ("kind", toJson "terminal"), ("id", toJson s.nextId), ("outcome", toJson outcome)]
    catch e =>
      (← IO.getStderr).putStrLn s!"task outcome (NOT durably saved): {(toJson outcome).compress}"
      throw e
    reportOutcome env.options s outcome
  | _ =>
    JournalIO.append (journalPath env.options) <| Json.mkObj [
      ("kind", toJson "intent"), ("id", toJson s.nextId), ("action", actionToJson node.1)]
    emit env.options s "intent" (actionToJson node.1)
    let reply ← interpret env s node.1
    JournalIO.append (journalPath env.options) <| Json.mkObj [
      ("kind", toJson "completion"), ("id", toJson s.nextId),
      ("observation", replyToJson node.1 reply)]
    emit env.options s "completion" (replyToJson node.1 reply)
    loop env (node.2 reply)

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

def start (o : Options) (config : Config) (task : String) : IO UInt32 := do
  let (session, workspace) ← validateSessionWorkspace o.session config.workspace
  let o := {o with session}
  let config := {config with workspace}
  JournalIO.createSession o.session
  withLock o do
    let identity ← implementationIdentity
    JournalIO.append (journalPath o) <| Json.mkObj [
      ("kind", toJson "initial"), ("schema", toJson (1 : Nat)),
      ("implementation", toJson identity), ("session", toJson o.session),
      ("config", toJson config), ("task", toJson task), ("script", toJson o.script)]
    loop {options := o, startedMs := ← IO.monoMsNow} (init o.session config task)

structure Loaded where
  cursor : Recovery.Cursor
  options : Options
  interruptedStorage : Bool

/-- Offline inspection/replay only needs the journal. Resume requests workspace
validation explicitly before it can advance or dispatch another operation. -/
def load (o : Options) (requireWorkspace : Bool := false) : IO Loaded := do
  let sessionPath ← canonicalSessionPath o.session
  let o := {o with session := sessionPath}
  let raw ← JournalIO.read (journalPath o)
  let records := raw.records
  let some initial := records[0]? | throw <| IO.userError "empty journal"
  unless (initial.getObjValAs? Nat "schema").toOption == some 1 do
    throw <| IO.userError "unsupported journal schema"
  unless (initial.getObjValAs? String "kind").toOption == some "initial" do
    throw <| IO.userError "missing initial record"
  let identity ← implementationIdentity
  unless (initial.getObjValAs? String "implementation").toOption == some identity do
    throw <| IO.userError "session requires the identical executable"
  let config : Config ← IO.ofExcept (initial.getObjValAs? Config "config")
  if requireWorkspace then
    let (_, workspace) ← validateSessionWorkspace o.session config.workspace
    unless workspace == config.workspace do
      throw <| IO.userError "saved workspace path no longer resolves to its frozen canonical identity"
  let task ← IO.ofExcept (initial.getObjValAs? String "task")
  let session ← IO.ofExcept (initial.getObjValAs? String "session")
  let script ← IO.ofExcept (initial.getObjValAs? (Option (Array Json)) "script")
  let cursor ← IO.ofExcept <| Recovery.replay (init session config task) (records.toList.drop 1)
  return {
    cursor, options := {o with script},
    interruptedStorage := raw.interrupted}

def inspect (o : Options) : IO UInt32 := withLock o do
  let loaded ← load o
  IO.println <| (Json.mkObj [("state", toJson loaded.cursor.state),
    ("pending", toJson loaded.cursor.pending), ("terminal", toJson loaded.cursor.terminal),
    ("interruptedStorage", toJson loaded.interruptedStorage)]).pretty
  return 0

def resume (o : Options) : IO UInt32 := withLock o do
  let loaded ← load o true
  if loaded.interruptedStorage then
    throw <| IO.userError "interrupted final storage record; preserve evidence; automatic resume refused"
  if loaded.cursor.pending then
    throw <| IO.userError "unresolved operation intent: outcome unknown; automatic replay of external work refused"
  if loaded.cursor.terminal then
    match (step loaded.cursor.state).1 with
    | .finish outcome => reportOutcome o loaded.cursor.state outcome
    | _ => throw <| IO.userError "invalid terminal state"
  else
    loop {options := loaded.options, startedMs := ← IO.monoMsNow} loaded.cursor.state

end Harness.Runner
