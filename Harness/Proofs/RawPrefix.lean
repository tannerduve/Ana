import Harness.Proofs.Transcript
import Harness.Proofs.RecoveryInvariant
import Mathlib.Data.List.Forall2

/-! An independent grammar for authoritative raw conversation prefixes. Partial
result messages consume the current batch in order. Active states expose exactly
the grammar's remaining IDs; terminal states may retain an unresolved suffix.
Ordinary reachability and accepted administrative replay both preserve this
property. It does not assert that incomplete terminal history is sendable, or that
JSON descriptor equality implies structural JSON equality. -/

namespace Harness

variable {app : Application}
open Lean
open ExceptRules

/-- A result block's grammar is independent of the execution phase and queue. -/
def ResultBlock (block : Json) (id : String) : Prop :=
  ∃ (text : String) (error : Bool), block = Json.mkObj
    [("type", toJson "tool_result"), ("tool_use_id", toJson id),
      ("content", toJson text), ("is_error", toJson error)]

/-- Ordered result blocks, each naming exactly one admitted call. -/
def ResultBlocks (blocks : List Json) (ids : List String) : Prop :=
  List.Forall₂ ResultBlock blocks ids

/-- Grammar of a raw conversation prefix. An open suffix records the outstanding
calls; it is not asserted sendable until that suffix is empty. Assistant content
uses the actual supported text/opaque/tool-use block parser, while results follow
in batch order and may occupy a partially filled final user message. -/
inductive RawPrefix : List Message → List String → Prop where
  | initial (text : String) : RawPrefix [{role := "user", content := #[textBlock text]}] []
  | user {base : List Message} (before : RawPrefix base []) (text : String) :
      RawPrefix (base ++ [{role := "user", content := #[textBlock text]}]) []
  | assistant {base : List Message} {content : Array Json} {calls : List RawCall} {text : String}
      (before : RawPrefix base []) (parsed : parseModelContent content = .ok (calls, text))
      (unique : (calls.map (·.id)).Nodup) :
      RawPrefix (base ++ [{role := "assistant", content}]) (calls.map (·.id))
  | results {base : List Message} {content : Array Json} {calls : List RawCall} {text : String}
      {blocks : List Json} {done remaining : List String}
      (before : RawPrefix base []) (parsed : parseModelContent content = .ok (calls, text))
      (unique : (calls.map (·.id)).Nodup)
      (completed : ResultBlocks blocks done) (nonempty : done ≠ [])
      (order : calls.map (·.id) = done ++ remaining) :
      RawPrefix (base ++ [{role := "assistant", content}, {role := "user", content := blocks.toArray}]) remaining

/-- A stopped prefix can retain unresolved calls; an active phase must expose
exactly its raw prefix's remaining ordered batch. -/
def RawHistoryValid (state : (State app)) : Prop :=
  match state.phase with
  | .stopped _ => ∃ remaining, RawPrefix state.history remaining
  | _ => RawPrefix state.history ((pendingCalls state).map (·.id))

/-- A closed prefix can be followed by another complete protocol segment. -/
private theorem paired_append_after_closed (messages suffix : List Message) (pending : List String)
    (closed : pairedMessages pending messages = true) :
    pairedMessages pending (messages ++ suffix) = pairedMessages [] suffix := by
  induction messages generalizing pending with
  | nil =>
    cases pending with
    | nil => rfl
    | cons _ _ => simp [pairedMessages] at closed
  | cons message rest ih =>
    by_cases user : (message.role == "user") = true
    · cases parsed : userResultIds message.content.toList false with
      | error error => simp [pairedMessages, user, parsed] at closed
      | ok ids =>
        simp only [pairedMessages, user, if_true, parsed, Bool.and_eq_true] at closed
        simp only [List.cons_append, pairedMessages, user, if_true, parsed, closed.1, Bool.true_and]
        exact ih [] closed.2
    · by_cases assistant : (message.role == "assistant" && pending.isEmpty) = true
      · cases parsed : parseModelContent message.content with
        | error error => simp [pairedMessages, user, assistant, parsed] at closed
        | ok decoded =>
          obtain ⟨calls,text⟩ := decoded
          simp only [pairedMessages, user, Bool.false_eq_true, if_false, assistant, if_true, parsed,
            Bool.and_eq_true] at closed
          simp only [List.cons_append, pairedMessages, user, Bool.false_eq_true, if_false,
            assistant, if_true, parsed, closed.1, Bool.true_and]
          exact ih _ closed.2
      · simp [pairedMessages, user, assistant] at closed

private theorem result_blocks_decode {blocks : List Json} {ids : List String}
    (valid : ResultBlocks blocks ids) : userResultIds blocks false = .ok ids := by
  induction valid with
  | nil => rfl
  | cons block rest ih =>
    obtain ⟨text,error,rfl⟩ := block
    change (do let tail ← userResultIds _ false; pure (_ :: tail)) = .ok _
    rw [ih]
    rfl

/-- The independent raw grammar identifies exactly whether all batch positions
are settled. A terminal open suffix cannot pass the executable closure check. -/
theorem raw_prefix_pairing {messages : List Message} {pending : List String}
    (valid : RawPrefix messages pending) : pairedMessages [] messages = pending.isEmpty := by
  induction valid with
  | initial text => rfl
  | user before text ih =>
    rw [paired_append_after_closed _ _ [] ih]
    rfl
  | assistant before parsed unique ih =>
    rw [paired_append_after_closed _ _ [] ih]
    simp [pairedMessages, parsed, unique]
  | @results base content calls text blocks done remaining before parsed unique completed nonempty order ih =>
    rw [paired_append_after_closed _ _ [] ih]
    simp only [pairedMessages, show ("assistant" == "user") = false from by decide,
      Bool.false_eq_true, ↓reduceIte, List.isEmpty_nil, Bool.and_true, beq_self_eq_true,
      parsed, unique, decide_true, Bool.true_and, result_blocks_decode completed]
    rw [order]
    by_cases empty : remaining = []
    · simp [empty]
    · have different : (done == done ++ remaining) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro equal
        have lengths := congrArg List.length equal
        simp only [List.length_append] at lengths
        have : remaining.length = 0 := by omega
        exact empty (List.length_eq_zero_iff.mp this)
      simp [different, empty]

private theorem raw_prefix_turn (before after : State app) (task : String)
    (valid : RawHistoryValid before) (accepted : beginTurn before task = .ok after) :
    RawHistoryValid after := by
  obtain ⟨equal, ready, closed, _⟩ := begin_turn_contract before after task accepted
  have stopped : ∃ outcome, before.phase = .stopped outcome := by
    cases phase : before.phase <;> simp [acceptsNewTurn, phase] at ready
    exact ⟨_, rfl⟩
  obtain ⟨outcome, phase⟩ := stopped
  obtain ⟨remaining, raw⟩ : ∃ remaining, RawPrefix before.history remaining := by
    simpa [RawHistoryValid, phase] using valid
  have paired : pairedMessages [] before.history = true := by
    cases history : before.history with
    | nil => simp [historyValid, history] at closed
    | cons first rest =>
      have both : (first.role == "user") = true ∧ pairedMessages [] (first :: rest) = true := by
        simpa [historyValid, history, Bool.and_eq_true] using closed
      exact both.2
  have empty : remaining = [] := by
    have := (raw_prefix_pairing raw).symm.trans paired
    exact List.isEmpty_iff.mp this
  rw [equal]
  exact RawPrefix.user (empty ▸ raw) task

private lemma parsed_ids' (response : ModelResponse)
    (valid : validateModelResponse response = .ok ()) :
    ∃ calls text, parseModelContent response.content = .ok (calls, text) ∧
      calls.map (·.id) = response.calls.map (·.id) := by
  obtain ⟨⟨calls,text⟩, parsed, equal, _⟩ := validateModelResponse_sound response valid
  refine ⟨calls, text, parsed, ?_⟩
  have ids := congrArg (List.map (fun (entry : String × String × String) => entry.1)) equal
  simpa only [List.map_map, Function.comp_def, RawCall.descriptor] using ids

lemma append_result_prefix (state : (State app)) (call : (Call app)) (text : String) (error : Bool)
    (remaining : List String) (valid : RawPrefix state.history (call.id :: remaining)) :
    RawPrefix (appendResult state call text error).history remaining := by
  generalize history : state.history = messages at valid
  generalize queue : call.id :: remaining = ids at valid
  cases valid with
  | initial task => simp at queue
  | user before text => simp at queue
  | assistant before parsed unique =>
    simp only [appendResult, history, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.nil_append]
    simp only [show ("assistant" == "user") = false from by decide, Bool.false_eq_true, if_false]
    rw [List.append_assoc]
    exact .results before parsed unique (.cons ⟨text,error,rfl⟩ .nil) (by simp) queue.symm
  | results before parsed unique completed nonempty order =>
    simp only [appendResult, history, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append]
    simp only [beq_self_eq_true, if_true, List.reverse_reverse,
      List.append_assoc]
    have single : ResultBlocks [Json.mkObj [("type", toJson "tool_result"),
        ("tool_use_id", toJson call.id), ("content", toJson text), ("is_error", toJson error)]] [call.id] :=
      .cons ⟨text,error,rfl⟩ .nil
    have blocks := List.rel_append completed single
    simp only [List.push_toArray]
    exact .results before parsed unique blocks (by simp) (by simpa [List.append_assoc, ← queue] using order)


@[simp] theorem prefix_advance (state : (State app)) : RawHistoryValid (advance state) = RawHistoryValid state := rfl

private lemma prefix_assistant (state : (State app)) (response : ModelResponse)
    (before : RawPrefix state.history []) (valid : validateModelResponse response = .ok ())
    (unique : (response.calls.map (·.id)).Nodup) :
    RawPrefix (state.history ++ [{role := "assistant", content := response.content}])
      (response.calls.map (·.id)) := by
  obtain ⟨calls,text,parsed,equal⟩ := parsed_ids' response valid
  exact equal ▸ RawPrefix.assistant before parsed (equal ▸ unique)

private theorem prefix_admitModel (state : (State app)) (raw : RawPrefix state.history []) :
    RawHistoryValid (admitModel state) := by
  unfold admitModel
  repeat' first | (exact raw) | (exact ⟨[],raw⟩) | split | (unfold admitTask; dsimp only) | unfold admitSummary

private theorem prefix_repair (state : (State app)) (kind : ResponseRepairKind) (message : String)
    (raw : RawPrefix state.history []) : RawHistoryValid (repairTaskResponse state kind message) := by
  unfold repairTaskResponse; split
  · exact RawPrefix.user raw (responseRepairText kind)
  · exact ⟨[],raw⟩

private theorem prefix_model (state : (State app)) (observation : ModelObservation)
    (raw : RawPrefix state.history []) : RawHistoryValid (consumeModel state observation) := by
  cases observation with
  | interrupted => exact ⟨[], raw⟩
  | uncertain message =>
    simp only [consumeModel]; unfold retryOrStop; split <;> (first | exact raw | exact ⟨[], raw⟩)
  | failure kind message =>
    cases kind <;> simp only [consumeModel]
    all_goals first | exact ⟨[],raw⟩ | exact prefix_repair _ _ _ raw | (unfold retryOrStop; split <;> (first | exact raw | exact ⟨[],raw⟩))
  | success response =>
    cases usage : response.usage <;> cases reason : response.stop <;>
      simp only [consumeModel, reason, usage, accountUsage]
    all_goals repeat' first | (exact ⟨[],raw⟩) | (exact prefix_repair _ _ _ raw) | split
    all_goals first
      | (rename_i accepted empty
         have unique : (response.calls.map (·.id)).Nodup := by simp [List.isEmpty_iff.mp empty]
         exact ⟨_, prefix_assistant state response raw accepted unique⟩)
      | (rename_i validated calls accepted
         obtain ⟨equal, unique, _⟩ := validated_batch_ids _ _ _ _ accepted
         change RawPrefix (state.history ++ [{role := "assistant", content := response.content}]) (calls.map (·.id))
         rw [equal]
         exact prefix_assistant state response raw (by assumption) (equal ▸ unique))

private theorem prefix_summary (state : (State app)) (plan : SummaryPlan) (observation : ModelObservation)
    (raw : RawPrefix state.history []) : RawHistoryValid (consumeSummary state plan observation) := by
  cases observation with
  | interrupted => exact ⟨[],raw⟩
  | uncertain message =>
    simp only [consumeSummary]; unfold retryOrStop; split <;> (first | exact raw | exact ⟨[],raw⟩)
  | failure kind message =>
    cases kind <;> simp only [consumeSummary]
    all_goals first | exact ⟨[],raw⟩ | (unfold retryOrStop; split <;> (first | exact raw | exact ⟨[],raw⟩))
  | success response =>
    cases usage : response.usage <;> cases reason : response.stop <;>
      simp only [consumeSummary, reason, usage, accountUsage]
    all_goals repeat' first | (exact raw) | (exact ⟨[],raw⟩) | split | (unfold installSummary; dsimp only)

theorem append_not_executed_prefix (state : (State app)) (remaining : List (Call app))
    (raw : RawPrefix state.history (remaining.map (·.id))) :
    RawPrefix (appendNotExecuted state remaining).history [] := by
  change RawPrefix (remaining.foldl _ state).history []
  induction remaining generalizing state with
  | nil => exact raw
  | cons call rest ih =>
    exact ih (appendResult state call timeoutSkippedText true)
      (append_result_prefix state call timeoutSkippedText true _ raw)

theorem cancellation_closes_raw_prefix (state : State app) (calls : List (Call app))
    (raw : RawPrefix state.history (calls.map (·.id))) :
    RawPrefix (cancelCalls state calls).history [] := by
  change RawPrefix (calls.foldl _ state).history []
  induction calls generalizing state with
  | nil => exact raw
  | cons call rest ih =>
    exact ih (appendResult state call cancelledCallText true)
      (append_result_prefix state call cancelledCallText true _ raw)

theorem timeout_closes_raw_prefix (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (partialResult : Option ToolResult)
    (raw : RawPrefix state.history (call.id :: remaining.map (·.id))) :
    RawPrefix (settleTimedOut state call remaining partialResult).history [] := by
  exact append_not_executed_prefix _ remaining
    (append_result_prefix state call _ true _ raw)

private theorem prefix_tool (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ToolObservation ToolResult)
    (raw : RawPrefix state.history (call.id :: remaining.map (·.id))) :
    RawHistoryValid (consumeTool state call remaining observation) := by
  cases observation <;> simp only [consumeTool, retainPartialArtifacts]
  all_goals repeat' first
    | (exact ⟨_,raw⟩)
    | (exact append_result_prefix _ call _ _ _ raw)
    | (exact timeout_closes_raw_prefix state call remaining _ raw)
    | split

private theorem prefix_approval (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ApprovalObservation)
    (raw : RawPrefix state.history (call.id :: remaining.map (·.id))) :
    RawHistoryValid (consumeApproval state call remaining observation) := by
  cases observation <;> simp only [consumeApproval]
  all_goals first | exact raw | exact ⟨[], cancellation_closes_raw_prefix state (call :: remaining) raw⟩ | exact append_result_prefix _ call _ _ _ raw

private theorem prefix_admitTool (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (raw : RawPrefix state.history (call.id :: remaining.map (·.id))) :
    RawHistoryValid (admitTool state call remaining) := by
  unfold admitTool
  repeat' first | (exact raw) | (exact ⟨_,raw⟩) | (exact append_result_prefix _ call _ _ _ raw) | split

private theorem prefix_controlModel (state : (State app)) (observation : ControlObservation)
    (raw : RawPrefix state.history []) : RawHistoryValid (consumeControl state none observation) := by
  simp only [consumeControl]
  split
  · exact ⟨[],raw⟩
  · split
    · exact ⟨[],raw⟩
    · exact prefix_admitModel state raw

private theorem prefix_controlTools (state : (State app)) (calls : List (Call app)) (observation : ControlObservation)
    (raw : RawPrefix state.history (calls.map (·.id))) :
    RawHistoryValid (consumeControl state (some calls) observation) := by
  simp only [consumeControl]
  split
  · exact ⟨[], cancellation_closes_raw_prefix state calls raw⟩
  · split
    · exact ⟨_,raw⟩
    · cases calls with
      | nil => exact raw
      | cons call remaining => exact prefix_admitTool state call remaining raw

private def PrefixNode (node : (HarnessF app) (State app)) : Prop :=
  ∀ response : Reply node.1, RawHistoryValid (node.2 response)

theorem raw_prefix_preserved (state : (State app)) (valid : RawHistoryValid state) :
    ∀ response : Reply (step state).1, RawHistoryValid ((step state).2 response) := by
  change PrefixNode (step state)
  cases phase : state.phase <;> simp only [step, phase]
  all_goals simp only [RawHistoryValid, phase, pendingCalls, List.map_cons] at valid
  case stopped outcome => intro response; exact response.elim
  case controlModel => exact fun response => prefix_controlModel state response valid
  case controlTools calls => exact fun response => prefix_controlTools state calls response valid
  case ask call remaining => exact fun response => prefix_approval state call remaining response valid
  case waiting delay => intro response; cases response <;> (first | exact valid | exact ⟨_, valid⟩)
  case model =>
    by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts)) = true
    · erw [if_pos admitted]; exact fun response => prefix_model state response valid
    · erw [if_neg admitted]; intro response; exact response.elim
  case summary =>
    cases pending : state.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts) && planValid state plan) = true
      · erw [if_pos admitted]; exact fun response => prefix_summary state plan response valid
      · erw [if_neg admitted]; intro response; exact response.elim
  case tool call remaining =>
    by_cases admitted : (authorized state.config state.grant call && artifactAuthorized state call && decide (0 < state.toolDispatches) && decide (state.toolDispatches ≤ state.config.maxToolCalls)) = true
    · erw [if_pos admitted]; exact fun response => prefix_tool state call remaining (response.map (app.render call.operation)) valid
    · erw [if_neg admitted]; intro response; exact response.elim

/-- Every ordinary reachable state has a valid raw prefix; active phases expose
its exact outstanding ordered batch. Terminal uncertainty may retain an open suffix. -/
theorem reachable_raw_prefix {id : String} {config : Config} {task : String} {state : (State app)}
    (reachable : Reachable id config task state) : RawHistoryValid state :=
  reachable.invariant (.initial task) raw_prefix_preserved

end Harness
namespace Harness

private theorem prefixRecoveryRules : Recovery.RecoveryRules (RawHistoryValid (app := app)) where
  step := raw_prefix_preserved
  userTurn := raw_prefix_turn
  clearGrant := fun _ valid => valid
  approvalRetry := by
    intro state valid call remaining phase
    simpa only [RawHistoryValid, pendingCalls, advance, phase] using valid
  artifactOverlay := fun _ _ valid _ _ _ => valid

/-- Accepted replay, including recovery and resolution, preserves the raw-prefix
grammar and its active-phase queue correspondence. A suspended position remains
tied to the exact uncertain continuation that created the current state. -/
theorem replay_raw_prefix (id : String) (config : Config) (task : String)
    (records : List Lean.Json) (next : Recovery.Cursor app)
    (accepted : Recovery.replay (init id config task app) records = .ok next) :
    Recovery.CursorProperty RawHistoryValid next :=
  Recovery.replay_property prefixRecoveryRules (init id config task app) (.initial task) records next accepted

end Harness
