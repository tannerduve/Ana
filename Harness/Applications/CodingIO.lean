import Harness.Core.Coding
import Harness.Adapter.ApplicationIO
import Harness.Adapter.ProcessIO

/-! Coding-specific filesystem, sandbox and edit-reconciliation adapters. The
generic Runner retains all scheduling, permissions and durable-record ordering. -/
namespace Harness.CodingIO
open Lean

private def prepareConfig (config : Config) : IO Config := do
  if config.workspace.isEmpty || config.workspace.contains '\x00' then
    throw <| IO.userError "workspace path must be nonempty and contain no NUL"
  let workspace ← IO.FS.realPath config.workspace
  unless (← workspace.metadata).type == .dir do
    throw <| IO.userError "workspace must be a directory"
  unless config.applicationData == Json.null do
    throw <| IO.userError "coding does not accept applicationData"
  return {config with workspace := workspace.toString}

private def validateIdentity (session : String) (config : Config) : IO Unit := do
  let (_, workspace) ← ApplicationIO.validateSessionWorkspace session config.workspace
  unless workspace == config.workspace do
    throw <| IO.userError "saved workspace path no longer resolves to its frozen canonical identity"
  unless config.applicationData == Json.null do
    throw <| IO.userError "coding does not accept applicationData"

private def validate (session : String) (config : Config) : IO Unit := do
  validateIdentity session config
  ProcessIO.validateSandbox config.workspace session config.executionProfile config.toolchainRoots

private def prepare (config : Config) (_ : ApplicationIO.OperationContext) (call : Call Coding.application) :
    IO (Option Coding.EditWitness) := do
  match call.operation with
  | .editFile args =>
    let (preimage, postimage) ← FilesystemIO.editIdentities config.workspace args
    return some {path := args.path, preimage, postimage}
  | _ => return none

private def reconcile (config : Config) (_ : ApplicationIO.OperationContext) (call : Call Coding.application)
    (witness : Option Coding.EditWitness) : IO Coding.Resolution := do
  match call.operation with
  | .editFile _ =>
    let some witness := witness
      | throw <| IO.userError "unresolved edit has no durable preimage/postimage witness"
    IO.ofExcept <| Coding.validateWitness call.operation witness
    let actual ← FilesystemIO.fileIdentity config.workspace witness.path
    if actual == witness.postimage then
      let settled ← FilesystemIO.confirmFileIdentity config.workspace witness.path actual
      return .editPostimage settled
    else if actual == witness.preimage then
      throw <| IO.userError "unresolved edit still matches preimage; execution is unstarted or had no lasting effect; automatic rerun refused"
    else
      throw <| IO.userError "unresolved edit conflicts with both saved preimage and intended postimage; automatic resume refused"
  | _ => throw <| IO.userError "unresolved operation outcome; process operations require explicit resolve; automatic rerun refused"

def runtime : ApplicationIO.Runtime Coding.application where
  prepareConfig := prepareConfig
  validateIdentity := validateIdentity
  validate := validate
  prepare := prepare
  reconcile := reconcile
  execute := fun _ context call => match call.operation with
    | .runProcess args => ProcessIO.run context args
    | _ => FilesystemIO.run context call

end Harness.CodingIO
