import Harness.Core.Policy

/-!
Explicit, serializable application-indexed session state: frozen config, raw history, optional compaction view
and pending summary plan, phase, operation ID, budget and usage counters, seen call IDs, a one-shot
approval grant and the artifact registry. `init` starts from one user task message; `stop` enters a
terminal phase and clears the grant.
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

inductive Phase (app : Application := Coding.application) where
  | controlModel
  | model
  | summary
  | controlTools (calls : List (Call app))
  | ask (call : Call app) (remaining : List (Call app))
  | tool (call : Call app) (remaining : List (Call app))
  | waiting (milliseconds : Nat)
  | stopped (outcome : Outcome)
  deriving Repr, ToJson, FromJson

structure State (app : Application := Coding.application) where
  schemaVersion : Nat := sessionSchemaVersion
  sessionId : String
  /-- Trusted user-turn index; ordinary execution never changes it. -/
  turn : Nat := 0
  config : Config
  history : List Message
  activeView : Option ContextView := none
  pendingSummary : Option SummaryPlan := none
  summaries : List SummaryRecord := []
  phase : Phase app := .controlModel
  nextId : Nat := 0
  modelAttempts : Nat := 0
  toolDispatches : Nat := 0
  retryCount : Nat := 0
  responseRepairs : Nat := 0
  knownInputTokens : Nat := 0
  knownOutputTokens : Nat := 0
  unknownUsage : Nat := 0
  seenCallIds : List String := []
  grant : Option (Call app) := none
  artifacts : List ArtifactRef := []
  deriving Repr, ToJson, FromJson

def textBlock (text : String) : Json := Json.mkObj [("type", toJson "text"), ("text", toJson text)]

def init (sessionId : String) (config : Config) (task : String) (app : Application := Coding.application) : State app :=
  { sessionId, config, history := [{role := "user", content := #[textBlock task]}] }

def stop {app : Application} (s : State app) (outcome : Outcome) : State app :=
  {s with phase := .stopped outcome, grant := none}

end Harness
