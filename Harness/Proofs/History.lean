import Harness.Proofs.Trace
import Harness.Proofs.Invariants
import Harness.Proofs.Validation

namespace Harness

variable {app : Application}

open ExceptRules

/-- The phase queue includes the current ask/tool position until its reply is
consumed. Stopped states have no executable queue, even if history is unresolved. -/
def pendingCalls (state : (State app)) : List (Call app) :=
  match state.phase with
  | .controlTools calls => calls
  | .ask call remaining | .tool call remaining => call :: remaining
  | _ => []

def CallsValid (state : (State app)) : Prop :=
  state.seenCallIds.Nodup ∧ ((pendingCalls state).map (·.id)).Nodup ∧
    ∀ call ∈ pendingCalls state, call.id ∈ state.seenCallIds

@[simp] theorem calls_advance (s : (State app)) : CallsValid (advance s) = CallsValid s := rfl

private theorem calls_empty (s : (State app)) (seen : s.seenCallIds.Nodup)
    (empty : pendingCalls s = []) : CallsValid s := by
  simp [CallsValid, empty, seen]

private theorem calls_subqueue (s next : (State app)) (valid : CallsValid s)
    (seen : next.seenCallIds = s.seenCallIds)
    (queue : List.Sublist (pendingCalls next) (pendingCalls s)) : CallsValid next := by
  refine ⟨seen ▸ valid.1, ?_, ?_⟩
  · exact (queue.map (·.id)).nodup valid.2.1
  · intro call member
    rw [seen]
    exact valid.2.2 call (queue.subset member)

private theorem calls_admitModel (s : (State app)) (valid : CallsValid s) : CallsValid (admitModel s) := by
  unfold admitModel
  repeat' first
    | (exact calls_empty _ valid.1 rfl)
    | split | (unfold admitTask; dsimp only) | unfold admitSummary

@[simp] theorem repair_pendingCalls (s : (State app)) (kind : ResponseRepairKind) (message : String) :
    pendingCalls (repairTaskResponse s kind message) = [] := by
  unfold repairTaskResponse; split <;> rfl

private theorem calls_repair (s : (State app)) (kind : ResponseRepairKind) (message : String)
    (seen : s.seenCallIds.Nodup) : CallsValid (repairTaskResponse s kind message) := by
  simp [CallsValid, seen]

private theorem calls_consumeModel (s : (State app)) (observation : ModelObservation)
    (valid : CallsValid s) : CallsValid (consumeModel s observation) := by
  cases observation with
  | interrupted => exact calls_empty _ valid.1 rfl
  | uncertain message =>
    simp only [consumeModel]
    unfold retryOrStop
    split <;> exact calls_empty _ valid.1 rfl
  | failure kind message =>
    cases kind <;> simp only [consumeModel]
    all_goals first
      | exact calls_empty _ valid.1 rfl
      | exact calls_repair _ _ _ valid.1
      | (unfold retryOrStop; split <;> exact calls_empty _ valid.1 rfl)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeModel, hs, hu, accountUsage]
    all_goals repeat' first | (exact calls_empty _ valid.1 rfl) | (exact calls_repair _ _ _ valid.1) | split
    all_goals
      rename_i calls accepted
      obtain ⟨_, distinct, fresh⟩ := validated_batch_ids _ _ _ _ accepted
      refine ⟨List.nodup_append.mpr ⟨valid.1, distinct, ?_⟩, distinct, ?_⟩
      · intro id old other member equal
        subst other
        exact fresh id member old
      · intro call member
        exact List.mem_append_right _ (List.mem_map.mpr ⟨call, member, rfl⟩)

private theorem calls_consumeSummary (s : (State app)) (plan : SummaryPlan) (observation : ModelObservation)
    (valid : CallsValid s) : CallsValid (consumeSummary s plan observation) := by
  cases observation with
  | interrupted => exact calls_empty _ valid.1 rfl
  | uncertain message =>
    simp only [consumeSummary]
    unfold retryOrStop
    split <;> exact calls_empty _ valid.1 rfl
  | failure kind message =>
    cases kind <;> simp only [consumeSummary]
    all_goals first
      | exact calls_empty _ valid.1 rfl
      | (unfold retryOrStop; split <;> exact calls_empty _ valid.1 rfl)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeSummary, hs, hu, accountUsage]
    all_goals repeat' first
      | (exact calls_empty _ valid.1 rfl)
      | split | (unfold installSummary; dsimp only)

private theorem calls_admitTool (s : (State app)) (call : (Call app)) (remaining : List (Call app))
    (valid : CallsValid s) (phase : s.phase = .controlTools (call :: remaining)) :
    CallsValid (admitTool s call remaining) := by
  unfold admitTool
  split
  · split
    · exact calls_subqueue s _ valid rfl (by simp [pendingCalls, phase])
    · split
      · exact calls_subqueue s _ valid rfl (by simp [pendingCalls, phase])
      · exact calls_subqueue s _ valid rfl (by simp [pendingCalls, phase])
  · exact calls_empty _ valid.1 rfl

private theorem calls_consumeTool (s : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ToolObservation ToolResult) (valid : CallsValid s)
    (phase : s.phase = .tool call remaining) : CallsValid (consumeTool s call remaining observation) := by
  cases observation <;> simp only [consumeTool, retainPartialArtifacts]
  all_goals repeat' first
    | (exact calls_empty _ valid.1 rfl)
    | (exact calls_subqueue s _ valid rfl (by simp [pendingCalls, phase]))
    | split

private theorem calls_consumeApproval (s : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ApprovalObservation) (valid : CallsValid s)
    (phase : s.phase = .ask call remaining) : CallsValid (consumeApproval s call remaining observation) := by
  cases observation <;> simp only [consumeApproval]
  all_goals first
    | exact calls_empty _ valid.1 rfl
    | exact calls_subqueue s _ valid rfl (by simp [pendingCalls, phase])

private theorem calls_controlModel (s : (State app)) (observation : ControlObservation) (valid : CallsValid s) :
    CallsValid (consumeControl s none observation) := by
  simp only [consumeControl]
  split
  · exact calls_empty _ valid.1 rfl
  · split
    · exact calls_empty _ valid.1 rfl
    · exact calls_admitModel s valid

private theorem calls_controlTools (s : (State app)) (calls : List (Call app)) (observation : ControlObservation)
    (valid : CallsValid s) (phase : s.phase = .controlTools calls) :
    CallsValid (consumeControl s (some calls) observation) := by
  simp only [consumeControl]
  split
  · exact calls_empty _ valid.1 rfl
  · split
    · exact calls_empty _ valid.1 rfl
    · cases calls with
      | nil => exact calls_empty _ valid.1 rfl
      | cons call remaining => exact calls_admitTool s call remaining valid phase

private def CallsNode (node : (HarnessF app) (State app)) : Prop :=
  ∀ response : Reply node.1, CallsValid (node.2 response)

theorem calls_preserved (state : (State app)) (valid : CallsValid state) :
    ∀ response : Reply (step state).1, CallsValid ((step state).2 response) := by
  change CallsNode (step state)
  cases phase : state.phase <;> simp only [step, phase]
  case stopped outcome => intro response; exact response.elim
  case controlModel => exact fun response => calls_controlModel state response valid
  case controlTools calls => exact fun response => calls_controlTools state calls response valid phase
  case ask call remaining => exact fun response => calls_consumeApproval state call remaining response valid phase
  case waiting delay =>
    intro response
    cases response <;> exact calls_empty _ valid.1 rfl
  case model =>
    by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts)) = true
    · erw [if_pos admitted]; exact fun response => calls_consumeModel state response valid
    · erw [if_neg admitted]; intro response; exact response.elim
  case summary =>
    cases pending : state.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts) && planValid state plan) = true
      · erw [if_pos admitted]; exact fun response => calls_consumeSummary state plan response valid
      · erw [if_neg admitted]; intro response; exact response.elim
  case tool call remaining =>
    by_cases admitted : (authorized state.config state.grant call && artifactAuthorized state call && decide (0 < state.toolDispatches) && decide (state.toolDispatches ≤ state.config.maxToolCalls)) = true
    · erw [if_pos admitted]; exact fun response => calls_consumeTool state call remaining (response.map (app.render call.operation)) valid phase
    · erw [if_neg admitted]; intro response; exact response.elim

theorem reachable_calls {id : String} {config : Config} {task : String} {state : (State app)}
    (reachable : Reachable id config task state) : CallsValid state := by
  exact reachable.invariant (by simp [CallsValid, pendingCalls, init]) calls_preserved

/-- A task inference phase carries the full admitted context, including the
artifact catalogue. Other phases may legitimately have unresolved tool calls. -/
def TaskHistoryValid (s : (State app)) : Prop :=
  match s.phase with
  | .model => historyValid (modelRequest s).messages = true
  | _ => True

private theorem taskHistory_admitTask (s : (State app)) : TaskHistoryValid (admitTask s) := by
  unfold admitTask
  dsimp only
  split
  · split
    · split
      · assumption
      · trivial
    · trivial
  · trivial

private theorem taskHistory_admitModel (s : (State app)) : TaskHistoryValid (admitModel s) := by
  unfold admitModel
  split
  · unfold admitSummary; split <;> (first | trivial | (split <;> trivial))
  · split
    · split
      · unfold admitSummary; split <;> (first | trivial | (split <;> trivial))
      · exact taskHistory_admitTask s
    · exact taskHistory_admitTask s

private theorem taskHistory_model (s : (State app)) (observation : ModelObservation) :
    TaskHistoryValid (consumeModel s observation) := by
  cases observation with
  | interrupted => trivial
  | uncertain message => simp only [consumeModel]; unfold retryOrStop; split <;> trivial
  | failure kind message =>
    cases kind <;> simp only [consumeModel]
    all_goals first | trivial | (unfold repairTaskResponse; split <;> trivial) | (unfold retryOrStop; split <;> trivial)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeModel, hs, hu, accountUsage]
    all_goals repeat' first | trivial | (unfold repairTaskResponse; split <;> trivial) | split

private theorem taskHistory_summary (s : (State app)) (plan : SummaryPlan) (observation : ModelObservation) :
    TaskHistoryValid (consumeSummary s plan observation) := by
  cases observation with
  | interrupted => trivial
  | uncertain message => simp only [consumeSummary]; unfold retryOrStop; split <;> trivial
  | failure kind message =>
    cases kind <;> simp only [consumeSummary]
    all_goals first | trivial | (unfold retryOrStop; split <;> trivial)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeSummary, hs, hu, accountUsage]
    all_goals repeat' first | trivial | split | (unfold installSummary; dsimp only)

private theorem taskHistory_control (s : (State app)) (calls : Option (List (Call app)))
    (observation : ControlObservation) : TaskHistoryValid (consumeControl s calls observation) := by
  simp only [consumeControl]
  split
  · trivial
  · split
    · trivial
    · cases calls with
      | none => exact taskHistory_admitModel s
      | some calls =>
        cases calls with
        | nil => trivial
        | cons call remaining =>
          dsimp only
          unfold admitTool
          repeat' first | trivial | split

private theorem taskHistory_tool (s : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ToolObservation ToolResult) : TaskHistoryValid (consumeTool s call remaining observation) := by
  cases observation <;> simp only [consumeTool]
  all_goals repeat' first | trivial | split

private def TaskHistoryNode (node : (HarnessF app) (State app)) : Prop :=
  ∀ response : Reply node.1, TaskHistoryValid (node.2 response)

theorem task_history_preserved (s : (State app)) :
    ∀ response : Reply (step s).1, TaskHistoryValid ((step s).2 response) := by
  change TaskHistoryNode (step s)
  cases phase : s.phase <;> simp only [step, phase]
  case stopped outcome => intro response; exact response.elim
  case controlModel => exact fun response => taskHistory_control s none response
  case controlTools calls => exact fun response => taskHistory_control s (some calls) response
  case ask call remaining => intro response; cases response <;> trivial
  case waiting delay => intro response; cases response <;> trivial
  case model =>
    by_cases admitted : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts)) = true
    · erw [if_pos admitted]; exact fun response => taskHistory_model s response
    · erw [if_neg admitted]; intro response; exact response.elim
  case summary =>
    cases pending : s.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases admitted : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts) && planValid s plan) = true
      · erw [if_pos admitted]; exact fun response => taskHistory_summary s plan response
      · erw [if_neg admitted]; intro response; exact response.elim
  case tool call remaining =>
    by_cases admitted : (authorized s.config s.grant call && artifactAuthorized s call && decide (0 < s.toolDispatches) && decide (s.toolDispatches ≤ s.config.maxToolCalls)) = true
    · erw [if_pos admitted]; exact fun response => taskHistory_tool s call remaining (response.map (app.render call.operation))
    · erw [if_neg admitted]; intro response; exact response.elim

theorem reachable_task_history {id : String} {config : Config} {task : String} {s : (State app)}
    (reachable : Reachable id config task s) : TaskHistoryValid s := by
  cases reachable with
  | initial => trivial
  | next previous response => exact task_history_preserved _ response

/-- The concrete request emitted by any reachable task phase has closed tool
pairing. This uses reachability, since serialized phases alone are untrusted. -/
theorem emitted_task_history_valid {id : String} {config : Config} {task : String}
    {s : (State app)} (reachable : Reachable id config task s) (request : ModelRequest)
    (emitted : (step s).1 = .model request) (purpose : request.purpose = .task) :
    historyValid request.messages = true := by
  have valid := reachable_task_history reachable
  cases phase : s.phase <;> simp only [step, phase] at emitted
  all_goals try contradiction
  case model =>
    by_cases admitted : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts)) = true
    · simp only [admitted] at emitted
      cases emitted
      simpa [TaskHistoryValid, phase] using valid
    · simp only [admitted] at emitted; contradiction
  case summary =>
    cases pending : s.pendingSummary with
    | none => simp [pending] at emitted
    | some plan =>
      simp only [pending] at emitted
      by_cases admitted : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts) && planValid s plan) = true
      · simp only [admitted] at emitted
        cases emitted
        cases purpose
      · simp only [admitted] at emitted; contradiction
  case tool call remaining =>
    by_cases admitted : (authorized s.config s.grant call && artifactAuthorized s call && decide (0 < s.toolDispatches) && decide (s.toolDispatches ≤ s.config.maxToolCalls)) = true
    · simp only [admitted] at emitted; contradiction
    · simp only [admitted] at emitted; contradiction

/-- A previously admitted identity that is no longer executable in the current
batch. Uncertain calls also leave ordinary execution; recovery is separate. -/
def RetiredCall (id : String) (s : (State app)) : Prop :=
  id ∈ s.seenCallIds ∧ id ∉ (pendingCalls s).map (·.id)

private theorem retired_empty (id : String) (s : (State app))
    (seen : id ∈ s.seenCallIds) (empty : pendingCalls s = []) : RetiredCall id s := by
  simp [RetiredCall, seen, empty]

private theorem retired_subqueue (id : String) (s next : (State app)) (retired : RetiredCall id s)
    (seen : next.seenCallIds = s.seenCallIds)
    (queue : List.Sublist (pendingCalls next) (pendingCalls s)) : RetiredCall id next := by
  refine ⟨seen ▸ retired.1, ?_⟩
  intro member
  exact retired.2 ((queue.map (·.id)).subset member)

private theorem retired_admitModel (id : String) (s : (State app)) (retired : RetiredCall id s) :
    RetiredCall id (admitModel s) := by
  unfold admitModel
  repeat' first
    | (exact retired_empty id _ retired.1 rfl)
    | split | (unfold admitTask; dsimp only) | unfold admitSummary

private theorem retired_repair (id : String) (s : (State app)) (kind : ResponseRepairKind)
    (message : String) (member : id ∈ s.seenCallIds) : RetiredCall id (repairTaskResponse s kind message) := by
  simp [RetiredCall, member]

private theorem retired_model (id : String) (s : (State app)) (observation : ModelObservation)
    (retired : RetiredCall id s) : RetiredCall id (consumeModel s observation) := by
  cases observation with
  | interrupted => exact retired_empty id _ retired.1 rfl
  | uncertain message => simp only [consumeModel]; unfold retryOrStop; split <;> exact retired_empty id _ retired.1 rfl
  | failure kind message =>
    cases kind <;> simp only [consumeModel]
    all_goals first
      | exact retired_empty id _ retired.1 rfl
      | exact retired_repair id _ _ _ retired.1
      | (unfold retryOrStop; split <;> exact retired_empty id _ retired.1 rfl)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeModel, hs, hu, accountUsage]
    all_goals repeat' first | (exact retired_empty id _ retired.1 rfl) | (exact retired_repair id _ _ _ retired.1) | split
    all_goals
      rename_i calls accepted
      obtain ⟨_, _, fresh⟩ := validated_batch_ids _ _ _ _ accepted
      exact ⟨List.mem_append_left _ retired.1, fun member => fresh id member retired.1⟩

private theorem retired_summary (id : String) (s : (State app)) (plan : SummaryPlan)
    (observation : ModelObservation) (retired : RetiredCall id s) :
    RetiredCall id (consumeSummary s plan observation) := by
  cases observation with
  | interrupted => exact retired_empty id _ retired.1 rfl
  | uncertain message => simp only [consumeSummary]; unfold retryOrStop; split <;> exact retired_empty id _ retired.1 rfl
  | failure kind message =>
    cases kind <;> simp only [consumeSummary]
    all_goals first
      | exact retired_empty id _ retired.1 rfl
      | (unfold retryOrStop; split <;> exact retired_empty id _ retired.1 rfl)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeSummary, hs, hu, accountUsage]
    all_goals repeat' first
      | (exact retired_empty id _ retired.1 rfl)
      | split | (unfold installSummary; dsimp only)

private theorem retired_control (id : String) (s : (State app)) (calls : Option (List (Call app)))
    (observation : ControlObservation) (retired : RetiredCall id s)
    (queue : ∀ pending, calls = some pending → pendingCalls s = pending) :
    RetiredCall id (consumeControl s calls observation) := by
  simp only [consumeControl]
  split
  · exact retired_empty id _ retired.1 rfl
  · split
    · exact retired_empty id _ retired.1 rfl
    · cases calls with
      | none => exact retired_admitModel id s retired
      | some calls =>
        have pending := queue calls rfl
        cases calls with
        | nil => exact retired_empty id _ retired.1 rfl
        | cons call remaining =>
          dsimp only
          unfold admitTool
          repeat' first
            | (exact retired_empty id _ retired.1 rfl)
            | (exact retired_subqueue id s _ retired rfl (by rw [pending]; simp [pendingCalls]))
            | split

private theorem retired_tool (id : String) (s : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ToolObservation ToolResult) (retired : RetiredCall id s)
    (phase : s.phase = .tool call remaining) : RetiredCall id (consumeTool s call remaining observation) := by
  cases observation <;> simp only [consumeTool, retainPartialArtifacts]
  all_goals repeat' first
    | (exact retired_empty id _ retired.1 rfl)
    | (exact retired_subqueue id s _ retired rfl (by simp [pendingCalls, phase]))
    | split

private def RetiredNode (id : String) (node : (HarnessF app) (State app)) : Prop :=
  ∀ response : Reply node.1, RetiredCall id (node.2 response)

theorem retired_call_preserved (id : String) (s : (State app)) (retired : RetiredCall id s) :
    ∀ response : Reply (step s).1, RetiredCall id ((step s).2 response) := by
  change RetiredNode id (step s)
  cases phase : s.phase <;> simp only [step, phase]
  case stopped outcome => intro response; exact response.elim
  case controlModel => exact fun response => retired_control id s none response retired (by simp)
  case controlTools calls =>
    exact fun response => retired_control id s (some calls) response retired (by intro _ equal; cases equal; simp [pendingCalls, phase])
  case ask call remaining =>
    intro response
    cases response <;> simp only [consumeApproval]
    all_goals first
      | exact retired_empty id _ retired.1 rfl
      | exact retired_subqueue id s _ retired rfl (by simp [pendingCalls, phase, advance])
  case waiting delay => intro response; cases response <;> exact retired_empty id _ retired.1 rfl
  case model =>
    by_cases admitted : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts)) = true
    · erw [if_pos admitted]; exact fun response => retired_model id s response retired
    · erw [if_neg admitted]; intro response; exact response.elim
  case summary =>
    cases pending : s.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases admitted : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts) && planValid s plan) = true
      · erw [if_pos admitted]; exact fun response => retired_summary id s plan response retired
      · erw [if_neg admitted]; intro response; exact response.elim
  case tool call remaining =>
    by_cases admitted : (authorized s.config s.grant call && artifactAuthorized s call && decide (0 < s.toolDispatches) && decide (s.toolDispatches ≤ s.config.maxToolCalls)) = true
    · erw [if_pos admitted]; exact fun response => retired_tool id s call remaining (response.map (app.render call.operation)) retired phase
    · erw [if_neg admitted]; intro response; exact response.elim

theorem ExecutionTrace.retired {first last : (State app)} {events : List (ObservedStep app)}
    (trace : ExecutionTrace first events last) (id : String) (retired : RetiredCall id first) :
    RetiredCall id last := by
  induction trace with
  | nil => exact retired
  | cons state response tail ih => exact ih (retired_call_preserved id state retired response)

theorem emitted_tool_pending (state : (State app)) (call : (Call app))
    (emitted : (step state).1 = .tool call) : call ∈ pendingCalls state := by
  cases phase : state.phase <;> simp only [step, phase] at emitted
  all_goals try contradiction
  case model =>
    by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts)) = true
    · simp only [admitted] at emitted; contradiction
    · simp only [admitted] at emitted; contradiction
  case summary =>
    cases pending : state.pendingSummary with
    | none => simp [pending] at emitted
    | some plan =>
      simp only [pending] at emitted
      by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts) && planValid state plan) = true
      · simp only [admitted] at emitted; contradiction
      · simp only [admitted] at emitted; contradiction
  case tool proposed remaining =>
    by_cases admitted : (authorized state.config state.grant proposed && artifactAuthorized state proposed && decide (0 < state.toolDispatches) && decide (state.toolDispatches ≤ state.config.maxToolCalls)) = true
    · simp only [admitted] at emitted
      cases emitted
      simp [pendingCalls, phase]
    · simp only [admitted] at emitted; contradiction

theorem emitted_tool_was_admitted {id : String} {config : Config} {task : String} {state : (State app)}
    (reachable : Reachable id config task state) (call : (Call app))
    (emitted : (step state).1 = .tool call) : call.id ∈ state.seenCallIds :=
  (reachable_calls reachable).2.2 call (emitted_tool_pending state call emitted)

theorem retired_call_never_dispatches {first last : (State app)} {events : List (ObservedStep app)}
    (trace : ExecutionTrace first events last) (call : (Call app))
    (retired : RetiredCall call.id first) : (step last).1 ≠ .tool call := by
  intro emitted
  exact (trace.retired call.id retired).2
    (List.mem_map.mpr ⟨call, emitted_tool_pending last call emitted, rfl⟩)

private theorem tool_reply_retires (state : (State app)) (call : (Call app)) (remaining : List (Call app))
    (valid : CallsValid state) (phase : state.phase = .tool call remaining)
    (response : ToolObservation ToolResult) : RetiredCall call.id (consumeTool state call remaining response) := by
  have admitted : call.id ∈ state.seenCallIds :=
    valid.2.2 call (by simp [pendingCalls, phase])
  have absent : call.id ∉ remaining.map (·.id) := by
    have distinct := valid.2.1
    have both : (call.id :: remaining.map (·.id)).Nodup := by
      simpa only [pendingCalls, phase, List.map_cons] using distinct
    exact (List.nodup_cons.mp both).1
  cases response <;> simp only [consumeTool, retainPartialArtifacts]
  all_goals repeat' first
    | (exact retired_empty call.id _ admitted rfl)
    | (exact ⟨admitted, absent⟩)
    | split

private def RetiresToolNode (node : (HarnessF app) (State app)) : Prop :=
  ∀ (response : Reply node.1) (call : (Call app)), node.1 = .tool call → RetiredCall call.id (node.2 response)

theorem emitted_tool_reply_retires (state : (State app)) (valid : CallsValid state) :
    ∀ (response : Reply (step state).1) (call : (Call app)),
      (step state).1 = .tool call → RetiredCall call.id ((step state).2 response) := by
  change RetiresToolNode (step state)
  cases phase : state.phase <;> simp only [step, phase]
  case stopped outcome => intro response; exact response.elim
  case controlModel => simp [RetiresToolNode]
  case controlTools calls => simp [RetiresToolNode]
  case ask call remaining => simp [RetiresToolNode]
  case waiting delay => simp [RetiresToolNode]
  case model =>
    by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts)) = true
    · erw [if_pos admitted]; simp [RetiresToolNode]
    · erw [if_neg admitted]; intro response; exact response.elim
  case summary =>
    cases pending : state.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts) && planValid state plan) = true
      · erw [if_pos admitted]; simp [RetiresToolNode]
      · erw [if_neg admitted]; intro response; exact response.elim
  case tool call remaining =>
    by_cases admitted : (authorized state.config state.grant call && artifactAuthorized state call && decide (0 < state.toolDispatches) && decide (state.toolDispatches ≤ state.config.maxToolCalls)) = true
    · erw [if_pos admitted]
      intro response proposed emitted
      cases emitted
      exact tool_reply_retires state call remaining valid phase (response.map (app.render call.operation))
    · erw [if_neg admitted]; intro response; exact response.elim

/-- A call identity can be dispatched at most once in ordinary execution. This
includes failed/interrupted replies and prevents retrying the same admitted call
under changed arguments. Administrative resolution does not dispatch operations. -/
theorem no_duplicate_tool_dispatch {id : String} {config : Config} {task : String}
    {first last : (State app)} {events : List (ObservedStep app)}
    (reachable : Reachable id config task first) (firstCall nextCall : (Call app))
    (response : Reply (step first).1) (firstEmitted : (step first).1 = .tool firstCall)
    (trace : ExecutionTrace ((step first).2 response) events last)
    (nextEmitted : (step last).1 = .tool nextCall) : firstCall.id ≠ nextCall.id := by
  intro same
  have retired := emitted_tool_reply_retires first (reachable_calls reachable) response firstCall firstEmitted
  have retiredNext : RetiredCall nextCall.id ((step first).2 response) := same ▸ retired
  exact retired_call_never_dispatches trace nextCall retiredNext nextEmitted

end Harness
