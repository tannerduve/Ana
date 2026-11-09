import Harness.Core.Policy

/-!
# Harness State

Defines the explicit, serializable state of a session. `State` stores the following fields:

- `config` and the authoritative `history`.
- An optional compaction `activeView` (`ContextView`), plus a `pendingSummary` plan
  (`SummaryPlan`).
- The completed `summaries` (`SummaryRecord`).
- The control `Phase` and the operation identity `nextId`.
- Attempt, dispatch, retry and usage counters.
- The seen call IDs and an optional one-shot approval `grant`.

`init` starts a session from a single user task message. `stop` moves to a terminal phase and
clears any grant. `textBlock` builds a text content block.
-/

namespace Harness
open Lean

structure ContextView where
  summary : Message
  sourceEnd : Nat
  deriving Repr, ToJson, FromJson

structure SummaryPlan where
  sourceStart : Nat
  sourceEnd : Nat
  previousSummary : Option Message
  deriving Repr, ToJson, FromJson

structure SummaryRecord where
  plan : SummaryPlan
  response : ModelResponse
  deriving Repr, ToJson, FromJson

inductive Phase where
  | controlModel
  | model
  | summary
  | controlTools (calls : List ToolCall)
  | ask (call : ToolCall) (remaining : List ToolCall)
  | tool (call : ToolCall) (remaining : List ToolCall)
  | waiting (milliseconds : Nat)
  | stopped (outcome : Outcome)
  deriving Repr, ToJson, FromJson

structure State where
  schemaVersion : Nat := 2
  sessionId : String
  config : Config
  history : List Message
  activeView : Option ContextView := none
  pendingSummary : Option SummaryPlan := none
  summaries : List SummaryRecord := []
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

def stop (s : State) (outcome : Outcome) : State :=
  {s with phase := .stopped outcome, grant := none}

end Harness
