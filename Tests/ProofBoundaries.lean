import Harness.Proofs.RawPrefix
import Harness.Proofs.ArtifactBounds

namespace Tests.ProofBoundaries
open Harness Lean

private theorem raw_nonempty {history : List Harness.Message} {ids : List String}
    (valid : RawPrefix history ids) : 0 < history.length := by
  cases valid <;> simp

private theorem initial_length_closed {history : List Harness.Message} {ids : List String}
    (valid : RawPrefix history ids) (length : history.length = 1) : ids = [] := by
  cases valid with
  | initial => rfl
  | user _ _ => rfl
  | assistant before parsed unique =>
    have positive := raw_nonempty before
    simp only [List.length_append, List.length_singleton] at length
    omega
  | results before parsed unique completed nonempty order =>
    simp only [List.length_append, List.length_cons, List.length_nil] at length
    omega

/-- Negative fixture: an initial user message does not authorize an orphaned
pending call, even though the standalone call is otherwise well formed. -/
example : ¬ RawHistoryValid (app := Coding.application)
    {init "fixture" {model := "fixture", workspace := "/fixture"} "task" with phase := .controlTools [{id := "orphan", operation := .readFile {path := "source.txt"}}]} := by
  intro valid
  have impossible := initial_length_closed valid rfl
  contradiction

private def resultBlock (id : String) : Json := Json.mkObj
  [("type", toJson "tool_result"), ("tool_use_id", toJson id),
   ("content", toJson "finished"), ("is_error", toJson false)]

/-- Negative fixture: a later result cannot stand in for the earlier batch head. -/
example : ¬ ResultBlocks [resultBlock "second", resultBlock "first"] ["first", "second"] := by
  intro valid
  cases valid with
  | cons head tail =>
    obtain ⟨text, error, equal⟩ := head
    have identity := congrArg resultId? equal
    change some "second" = some "first" at identity
    contradiction

example : ¬ ArtifactCallBounds
    {id := "empty-range", operation := .readArtifact {id := "stored", offset := 0, length := 0}} := by
  unfold ArtifactCallBounds
  decide

example : ¬ ArtifactCallBounds
    {id := "oversized-range", operation := .readArtifact {id := "stored", offset := 0, length := 65537}} := by
  unfold ArtifactCallBounds
  decide

/-- Nonzero offsets are deliberately not an admission rejection: the adapter
returns a typed error if this offset exceeds the retained artifact. -/
example : ArtifactCallBounds
    {id := "range", operation := .readArtifact {id := "stored", offset := 100000000, length := 1}} := by
  unfold ArtifactCallBounds
  decide

end Tests.ProofBoundaries
