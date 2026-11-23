import Harness.Core.Application
import Harness.Adapter.RuntimeTypes

/-! The typed application IO interface and shared trusted-session path checks.
An interpreter supplies resource validation, execution and reconciliation;
the Runner alone chooses actions and persists intents and observations. -/

namespace Harness.ApplicationIO
open Lean

private def resolveProspective (base : System.FilePath) : List String → IO System.FilePath
  | [] => pure base
  | "." :: rest => resolveProspective base rest
  | ".." :: rest => resolveProspective (base.parent.getD "/") rest
  | part :: rest => do
    -- FilePath joining preserves a root's trailing slash. If the first
    -- component is absent, realPath cannot remove that extra slash yet; saving
    -- it would change the session identity when the created path is reopened.
    let candidate := if base.toString == "/" then System.FilePath.mk ("/" ++ part) else base / part
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

/-- Stable identity shared by preparation, execution and reconciliation. The
runner supplies it; a model cannot choose an operation's durable key. -/
structure OperationContext where
  /-- Canonical durable session directory, owned by the runner. -/
  session : String
  sessionId : String
  /-- Logical operation ID, preserved across restart and reconciliation. -/
  operationId : Nat
  /-- Remaining validated batch, including this call, before preparation effects. -/
  batchTools : List String := []
  startedMs : Nat := 0
  timeoutMs : Nat := 0
  invocationDeadlineMs : Option Nat := none
  cancelPath : String := ""

/-- Application IO is invoked only by the shared durable runner. Reconciliation
returns evidence for pure validation; it never dispatches the lost operation. -/
structure Runtime (app : Application) where
  prepareConfig : Config → IO Config
  /-- Create application-owned resources in a newly created, locked session.
  Resume never calls this hook or recreates missing application state. -/
  initializeSession : String → Config → IO Unit := fun _ _ => pure ()
  /-- Identity checks only: explicit resolution must not launch a profile probe. -/
  validateIdentity : String → Config → IO Unit := fun _ _ => pure ()
  validate : String → Config → IO Unit
  execute : Config → ToolContext → (call : Call app) → IO (ToolObservation (app.Result call.operation))
  /-- Preparation may read evidence or persist private metadata, but must not
  dispatch an external mutation before the runner commits its intent. -/
  prepare : Config → OperationContext → Call app → IO (Option app.Witness) := fun _ _ _ => pure none
  reconcile : Config → OperationContext → Call app → Option app.Witness → IO app.Resolution := fun _ _ _ _ =>
    throw <| IO.userError "unresolved application operation; automatic replay refused"

end Harness.ApplicationIO
