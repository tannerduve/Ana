import Harness.Core.Policy

namespace Harness
open Lean

inductive Phase where
  | controlModel
  | model
  | controlTools (calls : List ToolCall)
  | ask (call : ToolCall) (remaining : List ToolCall)
  | tool (call : ToolCall) (remaining : List ToolCall)
  | waiting (milliseconds : Nat)
  | stopped (outcome : Outcome)
  deriving Repr, ToJson, FromJson

structure State where
  schemaVersion : Nat := 1
  sessionId : String
  config : Config
  history : List Message
  phase : Phase := .controlModel
  nextId : Nat := 0
  modelAttempts : Nat := 0
  toolDispatches : Nat := 0
  retryCount : Nat := 0
  knownInputTokens : Nat := 0
  knownOutputTokens : Nat := 0
  unknownUsage : Nat := 0
  seenCallIds : List String := []
  grant : Option ToolCall := none
  deriving Repr, ToJson, FromJson

def textBlock (text : String) : Json := Json.mkObj [("type", toJson "text"), ("text", toJson text)]

def init (sessionId : String) (config : Config) (task : String) : State :=
  { sessionId, config, history := [{role := "user", content := #[textBlock task]}] }

def modelRequest (s : State) : ModelRequest :=
  { model := s.config.model, system := s.config.instructions,
    messages := s.history, maxTokens := s.config.maxOutputTokens }

/-- Includes a conservative 16KiB allowance for the frozen coding-tool schemas and wire framing.
    This is a byte allowance, not an exact provider token count. -/
def contextBytes (s : State) : Nat := (toJson (modelRequest s)).compress.utf8ByteSize + 16384

/-- The first release stops explicitly rather than silently dropping context. -/
def contextAdmitted (s : State) : Bool := contextBytes s ≤ s.config.maxContextBytes

def stop (s : State) (outcome : Outcome) : State :=
  {s with phase := .stopped outcome, grant := none}

end Harness
