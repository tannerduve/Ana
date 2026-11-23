import Harness.Core.Coding

namespace Harness

/-- Trusted application mounts use fixed sandbox destinations, never model flags. -/
structure ResourceMount where
  name : String
  path : String
  readOnly : Bool := true
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- Parameters for carrying out one already-admitted tool operation. -/
structure ToolContext where
  /-- Trusted storage and operation identity supplied by the shared runner. -/
  sessionPath : String := ""
  sessionId : String := ""
  operationId : Nat := 0
  batchTools : List String := []
  workspace : String
  timeoutMs : Nat
  /-- Absolute monotonic invocation deadline; preparation must not reset it. -/
  invocationDeadlineMs : Option Nat := none
  /-- True only when the operation limit is strictly earlier than the invocation
  deadline. Equality remains an invocation deadline, never a recoverable timeout. -/
  localDeadline : Bool := false
  outputBytes : Nat
  artifactDir : String
  cancelPath : String
  executionProfile : ExecutionProfile := .host
  workspaceReadOnly : Bool := false
  resourceMounts : Array ResourceMount := #[]
  toolchainRoots : Array String := #[]
  maxArtifactBytes : Nat := 16 * 1024 * 1024
  maxSessionArtifactBytes : Nat := 64 * 1024 * 1024
  artifacts : List ArtifactRef := []

end Harness
