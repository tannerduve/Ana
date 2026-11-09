import Harness.Core.Coding

namespace Harness

/-- Parameters for carrying out one already-admitted tool operation. -/
structure ToolContext where
  /-- Trusted storage and operation identity supplied by the shared runner. -/
  sessionPath : String := ""
  sessionId : String := ""
  operationId : Nat := 0
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
  toolchainRoots : Array String := #[]
  maxArtifactBytes : Nat := 16 * 1024 * 1024
  maxSessionArtifactBytes : Nat := 64 * 1024 * 1024
  artifacts : List ArtifactRef := []

end Harness
