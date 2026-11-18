import Harness.Core.Capabilities

/-!
Serializable data types shared by the core and adapters: configuration, tool argument records and
operations, messages, model requests and responses, observations, artifact references and outcomes.
Contains JSON instances only, with no validation or transition logic.
-/

namespace Harness
open Lean

/-- Session schema is shared by creation, decoding and replay admission. -/
def sessionSchemaVersion : Nat := 7

instance : Repr Json where
  reprPrec j _ := j.compress

inductive CommandPolicy where
  | ask | allow | deny
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

inductive ExecutionProfile where
  | host | bubblewrap
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

inductive ModelBackend where
  | anthropic | claudeCode | codex
  deriving Repr, BEq, DecidableEq

instance : ToJson ModelBackend where
  toJson backend := toJson (match backend with
    | .anthropic => "anthropic" | .claudeCode => "claude-code" | .codex => "codex")

instance : FromJson ModelBackend where
  fromJson? value := do
    match ← value.getStr? with
    | "anthropic" => pure .anthropic
    | "claude-code" => pure .claudeCode
    | "codex" => pure .codex
    | _ => throw "modelBackend must be anthropic, claude-code, or codex"

structure Config where
  model : String
  modelBackend : ModelBackend := .anthropic
  instructions : String := "Use the available tools to complete the user's task. Check your work and explain the result."
  workspace : String := ""
  /-- Validated, nonsecret application data frozen at session creation. -/
  applicationData : Json := .null
  toolPolicy : CommandPolicy := .allow
  /-- Every ceiling must cover every declared tool capability. Empty means no
  additional ceiling; a single empty ceiling denies all tool operations. -/
  capabilityPolicy : Capability.Policy := []
  maxModelAttempts : Nat := 20
  maxToolCalls : Nat := 100
  maxContextBytes : Nat := 200000
  compactionEnabled : Bool := true
  compactAtPercent : Nat := 75
  compactionKeepMessages : Nat := 4
  maxSummaryBytes : Nat := 12000
  maxOutputTokens : Nat := 4096
  maxRetries : Nat := 2
  maxResponseRepairs : Nat := 2
  operationTimeoutMs : Nat := 120000
  maxToolOutputBytes : Nat := 65536
  maxResponseBytes : Nat := 2000000
  maxElapsedMs : Nat := 1800000
  maxBatchCalls : Nat := 32
  commands : CommandPolicy := .ask
  executionProfile : ExecutionProfile := .host
  toolchainRoots : Array String := #[]
  maxArtifactBytes : Nat := 16 * 1024 * 1024
  maxSessionArtifactBytes : Nat := 64 * 1024 * 1024
  testEndpoint : String := ""
  deriving Repr, ToJson, FromJson

structure ListArgs where
  path : String := "."
  limit : Nat := 200
  deriving Repr, BEq, DecidableEq, ToJson, FromJson
structure ReadArgs where
  path : String
  startLine : Nat := 1
  endLine : Nat := 200
  deriving Repr, BEq, DecidableEq, ToJson, FromJson
structure SearchArgs where
  query : String
  path : String := "."
  limit : Nat := 100
  caseSensitive : Bool := true
  deriving Repr, BEq, DecidableEq, ToJson, FromJson
structure EditArgs where
  path : String
  old : String
  new : String
  expectedSha256 : String
  deriving Repr, BEq, DecidableEq, ToJson, FromJson
structure CreateArgs where
  path : String
  content : String
  overwrite : Bool := false
  deriving Repr, BEq, DecidableEq, ToJson, FromJson
structure ProcessArgs where
  argv : Array String
  cwd : String := "."
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure ArtifactReadArgs where
  id : String
  offset : Nat := 0
  length : Nat := 4096
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure ArtifactRef where
  id : String
  sha256 : String
  label : String
  storedBytes : Nat
  totalBytes : Nat
  truncated : Bool
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

inductive ToolOp where
  | listFiles (args : ListArgs)
  | readFile (args : ReadArgs)
  | searchFiles (args : SearchArgs)
  | editFile (args : EditArgs)
  | createFile (args : CreateArgs)
  | runProcess (args : ProcessArgs)
  | readArtifact (args : ArtifactReadArgs)
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure RawCall where
  id : String
  name : String
  input : Json
  deriving Repr, ToJson, FromJson

def ToolOp.name : ToolOp → String
  | .listFiles _ => "list"
  | .readFile _ => "read"
  | .searchFiles _ => "search"
  | .editFile _ => "edit"
  | .createFile _ => "create"
  | .runProcess _ => "process"
  | .readArtifact _ => "artifact"

def ToolOp.args : ToolOp → Json
  | .listFiles a => toJson a
  | .readFile a => toJson a
  | .searchFiles a => toJson a
  | .editFile a => toJson a
  | .createFile a => toJson a
  | .runProcess a => toJson a
  | .readArtifact a => toJson a

structure Message where
  role : String
  content : Array Json
  deriving Repr, ToJson, FromJson

structure Usage where
  inputTokens : Nat
  outputTokens : Nat
  raw : Json := .null
  deriving Repr, ToJson, FromJson

inductive StopReason where
  | endTurn | toolUse | maxTokens | contextOverflow | refusal | other
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure ModelResponse where
  content : Array Json
  calls : List RawCall
  text : String
  stop : StopReason
  usage : Option Usage := none
  deriving Repr, ToJson, FromJson

inductive FailureClass where
  | rateLimit | transport | authentication | invalidRequest | contextOverflow | malformed | other
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

inductive ModelObservation where
  | success (response : ModelResponse)
  | failure (kind : FailureClass) (message : String)
  | interrupted
  | uncertain (message : String)
  deriving Repr, ToJson, FromJson

structure ToolResult where
  text : String
  exitCode : Option Int := none
  artifacts : Array ArtifactRef := #[]
  sha256 : Option String := none
  deriving Repr, ToJson, FromJson

inductive ToolObservation (α : Type) where
  | success (result : α)
  | failure (message : String)
  /-- The adapter established that a sandboxed command attempt has stopped after
  its local time limit. This does not assert rollback or the target's exit code. -/
  | timedOut (partialResult : Option α := none)
  | interrupted (message : String) (partialResult : Option α := none)
  | uncertain (message : String) (partialResult : Option α := none)
  deriving Repr, ToJson, FromJson

structure ControlObservation where
  cancelled : Bool := false
  deadlineExceeded : Bool := false
  monotonicMs : Nat := 0
  deriving Repr, ToJson, FromJson

inductive ApprovalObservation where
  | approved | denied | interrupted
  deriving Repr, ToJson, FromJson

inductive WaitObservation where
  | elapsed | interrupted
  deriving Repr, ToJson, FromJson

inductive Outcome where
  | final (answer : String)
  | failure (message : String)
  | cancelled
  | limit (message : String)
  | recoveryRequired (message : String)
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

inductive ModelPurpose where
  | task | summary
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure ModelRequest where
  model : String
  system : String
  messages : List Message
  maxTokens : Nat
  purpose : ModelPurpose := .task
  /-- Exact offered schemas are part of the admitted and journaled request. -/
  tools : Array Json := #[]
  deriving Repr, ToJson, FromJson

end Harness
