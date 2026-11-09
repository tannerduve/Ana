import Harness.Core.State
import Harness.Core.ModelResponse

/-!
Builds task and summary requests from `State` without rewriting raw `history`; `activeMessages`
substitutes the compaction summary for the summarized prefix. `requestBytes` is a conservative byte
estimate with a fixed framing allowance, not a token bound. Checks tool-use/result pairing and plans
summary boundaries that close tool batches and fit the context limit.
-/

namespace Harness
open Lean

variable {app : Application}

/-- The authoritative transcript is never rewritten by context compaction. -/
def activeMessages (s : State app) : List Message :=
  match s.activeView with
  | none => s.history
  | some view => view.summary :: s.history.drop view.sourceEnd

/-- Request-only limits from the ledger. In an emitted task request the current
attempt is already reserved; summaries and retries share the remaining budget. -/
def budgetMessage (s : State app) : Message :=
  {role := "user", content := #[textBlock
    (s!"[Harness limits] After this request, at most {s.config.maxModelAttempts - s.modelAttempts} further model requests and {s.config.maxToolCalls - s.toolDispatches} tool executions remain. " ++
      "Model requests include task responses, summaries, retries, and response repairs. " ++
      s!"This response is capped at {s.config.maxOutputTokens} output tokens. " ++
      s!"Configured operation time limit: {s.config.operationTimeoutMs} ms; cleanup may take additional time. " ++
      "The remaining invocation deadline may shorten this limit. " ++
      "An interrupted operation may have partial effects; inspect them before continuing. " ++
      "Prefer focused checks that fit the time limit. " ++
      "Inspecting tool results and then responding requires another model request. " ++
      "These limits do not grant permission.")]}

def modelRequest (s : State app) : ModelRequest :=
  let catalog := if s.artifacts.isEmpty then [] else
    [{role := "user", content := #[textBlock
      ("Retained tool output artifacts (use artifact with an ID and byte range to read):\n" ++
        (toJson s.artifacts).compress)]}]
  { model := s.config.model, system := s.config.instructions,
    messages := catalog ++ activeMessages s ++ [budgetMessage s],
    maxTokens := s.config.maxOutputTokens, purpose := .task, tools := app.schemas }

/-- Conservative byte admission, including the actual offered schemas and a 16KiB framing allowance.
This deliberately does not claim an exact provider token bound. -/
def requestBytes (request : ModelRequest) : Nat :=
  (toJson request).compress.utf8ByteSize + 16384

def contextBytes (s : State app) : Nat := requestBytes (modelRequest s)
def contextAdmitted (s : State app) : Bool := contextBytes s ≤ s.config.maxContextBytes

def userResultIds : List Json → Bool → Except String (List String)
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
  "Create a compact continuation summary of the preceding agent context. Preserve the user's objective and constraints, observed facts and their sources, actions taken, checks performed, unresolved failures, relevant identifiers, and next steps. Distinguish observed facts from guesses. Do not call tools or continue the task. Return only the summary as text."

def summarySource (s : State app) (plan : SummaryPlan) : List Message :=
  plan.previousSummary.toList ++ (s.history.drop plan.sourceStart).take (plan.sourceEnd - plan.sourceStart)

def summaryRequest (s : State app) (plan : SummaryPlan) : ModelRequest :=
  { model := s.config.model, system := s.config.instructions,
    messages := summarySource s plan ++ [{role := "user", content := #[textBlock summaryInstruction]}],
    maxTokens := s.config.maxOutputTokens, purpose := .summary }

def summaryView (plan : SummaryPlan) (response : ModelResponse) : ContextView :=
  { sourceEnd := plan.sourceEnd,
    summary := {role := "user", content := #[textBlock ("Continuation summary (may be incomplete):\n" ++ response.text)]} }

def planValid (s : State app) (plan : SummaryPlan) : Bool :=
  plan.sourceStart == (s.activeView.map (·.sourceEnd)).getD 0 &&
  (plan.previousSummary.map toJson).map Json.compress == (s.activeView.map (fun view => toJson view.summary)).map Json.compress &&
  plan.sourceStart < plan.sourceEnd && plan.sourceEnd ≤ s.history.length &&
  historyValid (summarySource s plan) &&
  historyValid ({role := "user", content := #[textBlock "summary"]} :: s.history.drop plan.sourceEnd) &&
  requestBytes (summaryRequest s plan) ≤ s.config.maxContextBytes

/-- Search only finite raw-history boundaries and retain at least the most recent
two messages. Both the summary source and retained suffix must close tool batches. -/
def planCompaction (s : State app) : Option SummaryPlan :=
  let limit := s.history.length - max 2 s.config.compactionKeepMessages
  let sourceStart := (s.activeView.map (·.sourceEnd)).getD 0
  let previousSummary := s.activeView.map (·.summary)
  ((List.range (limit + 1)).reverse.map fun sourceEnd =>
    ({ sourceStart, sourceEnd, previousSummary } : SummaryPlan)).find? (planValid s)

def wantsCompaction (s : State app) : Bool :=
  s.config.compactionEnabled &&
  contextBytes s * 100 ≥ s.config.maxContextBytes * max 1 (min 99 s.config.compactAtPercent)

end Harness
