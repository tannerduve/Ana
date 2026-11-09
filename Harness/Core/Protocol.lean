import Lean

/-!
# Protocol Data Types

Defines the serializable vocabulary shared by the core and adapters:

- `Config` holds limits, compaction settings and the `CommandPolicy`.
- `ListArgs`, `ReadArgs` and the other argument records carry tool arguments.
- `ToolOp`, `ToolCall` and `RawCall` represent tool calls.
- `Message`, `ModelRequest` and `ModelResponse` represent model exchanges.
- `ModelObservation`, `ToolObservation`, `ApprovalObservation`, `WaitObservation` and
  `ControlObservation` are the observation types.
- `Outcome` lists terminal results.

These are plain data definitions with JSON instances. This module contains no validation or
transition logic.
-/

namespace Harness
open Lean

instance : Repr Json where
  reprPrec j _ := j.compress

inductive CommandPolicy where
  | ask | allow | deny
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure Config where
  model : String
  instructions : String := "You are a coding agent. Inspect files before editing; run relevant tests; explain your result."
  workspace : String
  maxModelAttempts : Nat := 20
  maxToolCalls : Nat := 100
  maxContextBytes : Nat := 200000
  compactionEnabled : Bool := true
  compactAtPercent : Nat := 75
  compactionKeepMessages : Nat := 4
  maxSummaryBytes : Nat := 12000
  maxOutputTokens : Nat := 4096
  maxRetries : Nat := 2
  operationTimeoutMs : Nat := 120000
  maxToolOutputBytes : Nat := 65536
  maxResponseBytes : Nat := 2000000
  maxElapsedMs : Nat := 1800000
  maxBatchCalls : Nat := 32
  commands : CommandPolicy := .ask
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

inductive ToolOp where
  | listFiles (args : ListArgs)
  | readFile (args : ReadArgs)
  | searchFiles (args : SearchArgs)
  | editFile (args : EditArgs)
  | createFile (args : CreateArgs)
  | runProcess (args : ProcessArgs)
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure ToolCall where
  id : String
  operation : ToolOp
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

def ToolOp.args : ToolOp → Json
  | .listFiles a => toJson a
  | .readFile a => toJson a
  | .searchFiles a => toJson a
  | .editFile a => toJson a
  | .createFile a => toJson a
  | .runProcess a => toJson a

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
  artifact : Option String := none
  sha256 : Option String := none
  deriving Repr, ToJson, FromJson

inductive ToolObservation (α : Type) where
  | success (result : α)
  | failure (message : String)
  | interrupted (message : String)
  | uncertain (message : String)
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
  deriving Repr, ToJson, FromJson

end Harness
