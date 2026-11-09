import Harness.Core.Context

/-!
Trusted follow-up admission is separate from ordinary execution. It extends a
completed conversation without replacing configuration, refunding budgets or
reviving approval. Cancellation closes undispatched calls in `Transition`;
uncertain effects must be resolved before this boundary can be used.
-/
namespace Harness
open Lean

variable {app : Application}

def acceptsNewTurn (s : State app) : Bool :=
  match s.phase with
  | .stopped (.final _) | .stopped .cancelled => true
  | _ => false

def turnCandidate (s : State app) (task : String) : State app :=
  {s with
    turn := s.turn + 1, nextId := s.nextId + 1,
    history := s.history ++ [{role := "user", content := #[textBlock task]}],
    phase := .controlModel, grant := none, retryCount := 0, pendingSummary := none}

/-- This input is supplied by the trusted user channel, never a model reply.
The next control observation still checks cancellation and invocation deadline;
the next model attempt is reserved by ordinary admission, not by this function. -/
def beginTurn (s : State app) (task : String) : Except String (State app) := do
  unless acceptsNewTurn s do throw "a follow-up requires a final or settled cancelled turn"
  if task.trimAscii.toString.isEmpty then throw "follow-up task must be nonempty"
  if task.utf8ByteSize > s.config.maxContextBytes then throw "follow-up task exceeds context byte allowance"
  unless s.modelAttempts < s.config.maxModelAttempts do throw "session model attempt ceiling exhausted"
  unless historyValid s.history do throw "follow-up requires a closed raw transcript"
  let next := turnCandidate s task
  unless historyValid (activeMessages next) do throw "follow-up active context has invalid tool pairing"
  return next

end Harness
