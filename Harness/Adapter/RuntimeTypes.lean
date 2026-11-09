import Harness.Core.Protocol

namespace Harness

/-- Parameters for carrying out one already-admitted tool operation. -/
structure ToolContext where
  workspace : String
  timeoutMs : Nat
  outputBytes : Nat
  artifactDir : String
  cancelPath : String

end Harness
