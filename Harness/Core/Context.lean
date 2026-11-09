import Harness.Core.State
import Harness.Core.ModelResponse

/-!
# Active Context and Compaction Planning

Builds model requests from `State` without rewriting the authoritative `history`.
`activeMessages` replaces the summarized prefix with the `ContextView` summary. `requestBytes`
estimates request size from compressed JSON bytes plus a fixed 16KiB allowance. It is a byte
estimator, not an exact provider token bound. `contextAdmitted` and `wantsCompaction` compare
this estimate with configured limits.

`pairedMessages` and `historyValid` check tool-use/tool-result pairing. `planValid` and
`planCompaction` select summary boundaries that close tool batches. `summaryRequest` and
`summaryView` construct the compaction request and its resulting view.
-/

namespace Harness
open Lean

/-- The authoritative transcript is never rewritten by context compaction. -/
def activeMessages (s : State) : List Message :=
  match s.activeView with
  | none => s.history
  | some view => view.summary :: s.history.drop view.sourceEnd

def modelRequest (s : State) : ModelRequest :=
  { model := s.config.model, system := s.config.instructions,
    messages := activeMessages s, maxTokens := s.config.maxOutputTokens, purpose := .task }

/-- Conservative byte admission, including 16KiB for tool schemas and framing.
This deliberately does not claim an exact provider token bound. -/
def requestBytes (request : ModelRequest) : Nat :=
  (toJson request).compress.utf8ByteSize + 16384

def contextBytes (s : State) : Nat := requestBytes (modelRequest s)
def contextAdmitted (s : State) : Bool := contextBytes s ≤ s.config.maxContextBytes

private def userResultIds : List Json → Bool → Except String (List String)
  | [], _ => .ok []
  | block :: rest, textSeen => do
    let kind ← block.getObjValAs? String "type"
    if kind == "text" then
      let _ ← block.getObjValAs? String "text"
      userResultIds rest true
    else if kind == "tool_result" && !textSeen then
      let id ← block.getObjValAs? String "tool_use_id"
      let _ ← block.getObjValAs? String "content"
      return id :: (← userResultIds rest false)
    else .error "invalid user block or tool-result ordering"

/-- Pending IDs must be completed exactly once in the next user message, in
admitted order; results precede any ordinary user text. -/
def pairedMessages : List String → List Message → Bool
  | pending, [] => pending.isEmpty
  | pending, message :: rest =>
    if message.role == "user" then
      match userResultIds message.content.toList false with
      | .error _ => false
      | .ok ids => ids == pending && pairedMessages [] rest
    else if message.role == "assistant" && pending.isEmpty then
      match parseModelContent message.content with
      | .error _ => false
      | .ok (calls, _) =>
        let ids := calls.map (·.id)
        ids.Nodup && pairedMessages ids rest
    else false

/-- Supported message-shape contract, including a leading user message and no
unresolved tool calls. It is stricter than providers that permit result reordering. -/
def historyValid (messages : List Message) : Bool :=
  match messages with
  | [] => false
  | first :: _ => first.role == "user" && pairedMessages [] messages

def summaryInstruction : String :=
  "Create a compact continuation summary of the preceding coding-agent context. Preserve the user's objective and constraints, repository facts, changes made, test results, unresolved failures, relevant paths, and next steps. Distinguish observed facts from guesses. Do not call tools or continue the task. Return only the summary as text."

def summarySource (s : State) (plan : SummaryPlan) : List Message :=
  plan.previousSummary.toList ++ (s.history.drop plan.sourceStart).take (plan.sourceEnd - plan.sourceStart)

def summaryRequest (s : State) (plan : SummaryPlan) : ModelRequest :=
  { model := s.config.model, system := s.config.instructions,
    messages := summarySource s plan ++ [{role := "user", content := #[textBlock summaryInstruction]}],
    maxTokens := s.config.maxOutputTokens, purpose := .summary }

def summaryView (plan : SummaryPlan) (response : ModelResponse) : ContextView :=
  { sourceEnd := plan.sourceEnd,
    summary := {role := "user", content := #[textBlock ("Continuation summary (may be incomplete):\n" ++ response.text)]} }

def planValid (s : State) (plan : SummaryPlan) : Bool :=
  plan.sourceStart == (s.activeView.map (·.sourceEnd)).getD 0 &&
  (plan.previousSummary.map toJson).map Json.compress == (s.activeView.map (fun view => toJson view.summary)).map Json.compress &&
  plan.sourceStart < plan.sourceEnd && plan.sourceEnd ≤ s.history.length &&
  historyValid (summarySource s plan) &&
  historyValid ({role := "user", content := #[textBlock "summary"]} :: s.history.drop plan.sourceEnd) &&
  requestBytes (summaryRequest s plan) ≤ s.config.maxContextBytes

/-- Search only finite raw-history boundaries and retain at least the most recent
two messages. Both the summary source and retained suffix must close tool batches. -/
def planCompaction (s : State) : Option SummaryPlan :=
  let limit := s.history.length - max 2 s.config.compactionKeepMessages
  let sourceStart := (s.activeView.map (·.sourceEnd)).getD 0
  let previousSummary := s.activeView.map (·.summary)
  ((List.range (limit + 1)).reverse.map fun sourceEnd =>
    ({ sourceStart, sourceEnd, previousSummary } : SummaryPlan)).find? (planValid s)

def wantsCompaction (s : State) : Bool :=
  s.config.compactionEnabled &&
  contextBytes s * 100 ≥ s.config.maxContextBytes * max 1 (min 99 s.config.compactAtPercent)

end Harness
