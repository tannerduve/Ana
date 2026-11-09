import Harness.Proofs.ApplicationCoding
import Harness.Proofs.History
import Harness.Proofs.Artifacts
import Harness.Proofs.Administrative

/-! Artifact-read admission bounds follow from the executable decoder through the
real batch validator and pending queues. Both ordinary reachability and accepted
administrative replay preserve them. Requested lengths are 1..65536 bytes;
offsets beyond retained data remain permitted and receive typed adapter errors.
Registry authority and dispatch ceilings are combined with the length result. -/

namespace Harness
open ExceptRules

def ArtifactCallBounds (call : ToolCall) : Prop :=
  match call.operation with
  | .readArtifact args => 1 ≤ args.length ∧ args.length ≤ 65536
  | _ => True

def ArtifactOperationBounds (op : ToolOp) : Prop :=
  match op with
  | .readArtifact args => 1 ≤ args.length ∧ args.length ≤ 65536
  | _ => True

theorem decode_operation_artifact_bounds (raw : RawCall) :
    ExceptSuccess ArtifactOperationBounds (decodeOperation raw) := by
  intro operation accepted
  have valid := Coding.decode_valid raw operation accepted
  cases operation <;> simp_all [ArtifactOperationBounds, Coding.ValidOperation]
  omega

theorem decoded_call_artifact_bounds (raw : RawCall) (call : ToolCall)
    (accepted : decodeCall raw = .ok call) : ArtifactCallBounds call := by
  by_cases empty : raw.id.isEmpty = true
  · simp [decodeCall, empty] at accepted
  · cases decoded : decodeOperation raw with
    | error message => simp [decodeCall, empty, Coding.application, decoded] at accepted
    | ok operation =>
      have bound := decode_operation_artifact_bounds raw operation decoded
      simp only [decodeCall, empty, Coding.application, decoded, ok_bind,
        pure_ok] at accepted
      cases accepted
      exact bound


def PendingArtifactBounds (state : State) : Prop :=
  ∀ call ∈ pendingCalls state, ArtifactCallBounds call

@[simp] theorem bounds_advance (s : State) : PendingArtifactBounds (advance s) = PendingArtifactBounds s := rfl

private theorem bounds_empty (s : State) (empty : pendingCalls s = []) : PendingArtifactBounds s := by
  simp [PendingArtifactBounds, empty]

private theorem bounds_subqueue (s next : State) (valid : PendingArtifactBounds s)
    (queue : List.Sublist (pendingCalls next) (pendingCalls s)) : PendingArtifactBounds next := by
  exact fun call member => valid call (queue.subset member)

private theorem bounds_admitModel (s : State) (_valid : PendingArtifactBounds s) : PendingArtifactBounds (admitModel s) := by
  unfold admitModel
  repeat' first
    | (exact bounds_empty _ rfl)
    | split | (unfold admitTask; dsimp only) | unfold admitSummary

private theorem bounds_consumeModel (s : State) (observation : ModelObservation)
    (_valid : PendingArtifactBounds s) : PendingArtifactBounds (consumeModel s observation) := by
  cases observation with
  | interrupted => exact bounds_empty _ rfl
  | uncertain message =>
    simp only [consumeModel]
    unfold retryOrStop
    split <;> exact bounds_empty _ rfl
  | failure kind message =>
    cases kind <;> simp only [consumeModel]
    all_goals first
      | exact bounds_empty _ rfl
      | exact bounds_empty _ (repair_pendingCalls _ _ _)
      | (unfold retryOrStop; split <;> exact bounds_empty _ rfl)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeModel, hs, hu, accountUsage]
    all_goals repeat' first | (exact bounds_empty _ rfl) | (exact bounds_empty _ (repair_pendingCalls _ _ _)) | (split)
    all_goals
      rename_i calls accepted
      exact validated_batch_all ArtifactCallBounds decoded_call_artifact_bounds _ _ _ _ accepted

private theorem bounds_consumeSummary (s : State) (plan : SummaryPlan) (observation : ModelObservation)
    (_valid : PendingArtifactBounds s) : PendingArtifactBounds (consumeSummary s plan observation) := by
  cases observation with
  | interrupted => exact bounds_empty _ rfl
  | uncertain message =>
    simp only [consumeSummary]
    unfold retryOrStop
    split <;> exact bounds_empty _ rfl
  | failure kind message =>
    cases kind <;> simp only [consumeSummary]
    all_goals first
      | exact bounds_empty _ rfl
      | (unfold retryOrStop; split <;> exact bounds_empty _ rfl)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeSummary, hs, hu, accountUsage]
    all_goals repeat' first
      | (exact bounds_empty _ rfl)
      | split | (unfold installSummary; dsimp only)

private theorem bounds_admitTool (s : State) (call : ToolCall) (remaining : List ToolCall)
    (valid : PendingArtifactBounds s) (phase : s.phase = .controlTools (call :: remaining)) :
    PendingArtifactBounds (admitTool s call remaining) := by
  unfold admitTool
  split
  · split
    · exact bounds_subqueue s _ valid (by simp [pendingCalls, phase])
    · split
      · exact bounds_subqueue s _ valid (by simp [pendingCalls, phase])
      · exact bounds_subqueue s _ valid (by simp [pendingCalls, phase])
  · exact bounds_empty _ rfl

private theorem bounds_consumeTool (s : State) (call : ToolCall) (remaining : List ToolCall)
    (observation : ToolObservation ToolResult) (valid : PendingArtifactBounds s)
    (phase : s.phase = .tool call remaining) : PendingArtifactBounds (consumeTool s call remaining observation) := by
  have tail : ∀ proposed ∈ remaining, ArtifactCallBounds proposed := by
    intro proposed member
    exact valid proposed (by simp [pendingCalls, phase, member])
  cases observation <;> simp only [consumeTool, retainPartialArtifacts]
  all_goals repeat' first | (exact bounds_empty _ rfl) | (exact tail) | split

private theorem bounds_consumeApproval (s : State) (call : ToolCall) (remaining : List ToolCall)
    (observation : ApprovalObservation) (valid : PendingArtifactBounds s)
    (phase : s.phase = .ask call remaining) : PendingArtifactBounds (consumeApproval s call remaining observation) := by
  cases observation <;> simp only [consumeApproval]
  all_goals first
    | exact bounds_empty _ rfl
    | exact bounds_subqueue s _ valid (by simp [pendingCalls, phase])

private theorem bounds_controlModel (s : State) (observation : ControlObservation) (valid : PendingArtifactBounds s) :
    PendingArtifactBounds (consumeControl s none observation) := by
  simp only [consumeControl]
  split
  · exact bounds_empty _ rfl
  · split
    · exact bounds_empty _ rfl
    · exact bounds_admitModel s valid

private theorem bounds_controlTools (s : State) (calls : List ToolCall) (observation : ControlObservation)
    (valid : PendingArtifactBounds s) (phase : s.phase = .controlTools calls) :
    PendingArtifactBounds (consumeControl s (some calls) observation) := by
  simp only [consumeControl]
  split
  · exact bounds_empty _ rfl
  · split
    · exact bounds_empty _ rfl
    · cases calls with
      | nil => exact bounds_empty _ rfl
      | cons call remaining => exact bounds_admitTool s call remaining valid phase

private def CallsNode (node : HarnessF Coding.application State) : Prop :=
  ∀ response : Reply node.1, PendingArtifactBounds (node.2 response)

theorem artifact_bounds_preserved (state : State) (valid : PendingArtifactBounds state) :
    ∀ response : Reply (step state).1, PendingArtifactBounds ((step state).2 response) := by
  change CallsNode (step state)
  cases phase : state.phase <;> simp only [step, phase]
  case stopped outcome => intro response; exact response.elim
  case controlModel => exact fun response => bounds_controlModel state response valid
  case controlTools calls => exact fun response => bounds_controlTools state calls response valid phase
  case ask call remaining => exact fun response => bounds_consumeApproval state call remaining response valid phase
  case waiting delay =>
    intro response
    cases response <;> exact bounds_empty _ rfl
  case model =>
    by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts)) = true
    · erw [if_pos admitted]; exact fun response => bounds_consumeModel state response valid
    · erw [if_neg admitted]; intro response; exact response.elim
  case summary =>
    cases pending : state.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts) && planValid state plan) = true
      · erw [if_pos admitted]; exact fun response => bounds_consumeSummary state plan response valid
      · erw [if_neg admitted]; intro response; exact response.elim
  case tool call remaining =>
    by_cases admitted : (authorized state.config state.grant call && artifactAuthorized state call && decide (0 < state.toolDispatches) && decide (state.toolDispatches ≤ state.config.maxToolCalls)) = true
    · erw [if_pos admitted]; exact fun response => bounds_consumeTool state call remaining (response.map (Coding.application.render call.operation)) valid phase
    · erw [if_neg admitted]; intro response; exact response.elim


theorem reachable_artifact_bounds {id : String} {config : Config} {task : String} {state : State}
    (reachable : Reachable id config task state) : PendingArtifactBounds state := by
  exact reachable.invariant (by simp [PendingArtifactBounds, pendingCalls, init]) artifact_bounds_preserved

/-- Range admission is bounded by the decoder, not by the IO result. Offsets
beyond the retained artifact remain permitted and receive typed IO errors. -/
theorem emitted_artifact_read_bounded {id : String} {config : Config} {task : String} {state : State}
    (reachable : Reachable id config task state) (call : ToolCall) (args : ArtifactReadArgs)
    (operation : call.operation = .readArtifact args) (emitted : (step state).1 = .tool call) :
    (1 ≤ args.length ∧ args.length ≤ 65536) ∧
      (∃ ref ∈ state.artifacts, ref.id = args.id) ∧
      state.toolDispatches ≤ state.config.maxToolCalls := by
  have bounded := reachable_artifact_bounds reachable call (emitted_tool_pending state call emitted)
  exact ⟨by simpa [ArtifactCallBounds, operation] using bounded,
    emitted_artifact_read_registered state call args operation emitted,
    (reachable_budgets reachable).2⟩

end Harness

namespace Harness

private theorem boundsRecoveryRules : Recovery.RecoveryRules PendingArtifactBounds where
  step := artifact_bounds_preserved
  clearGrant := fun _ valid => valid
  approvalRetry := by
    intro state valid call remaining phase
    simpa only [PendingArtifactBounds, pendingCalls, advance, phase] using valid
  userTurn := by
    intro before after task _ accepted
    rw [(begin_turn_contract before after task accepted).1]
    simp [PendingArtifactBounds, pendingCalls, turnCandidate]
  artifactOverlay := fun _ _ valid _ _ _ => valid

theorem replay_artifact_bounds (id : String) (config : Config) (task : String)
    (records : List Lean.Json) (next : Recovery.Cursor)
    (accepted : Recovery.replay (init id config task) records = .ok next) :
    Recovery.CursorProperty PendingArtifactBounds next :=
  Recovery.replay_property boundsRecoveryRules (init id config task)
    (by simp [PendingArtifactBounds, pendingCalls, init]) records next accepted

/-- Accepted administrative replay emits artifact reads only with bounded requested
length, an admitted registry identity, and a valid dispatch ceiling. -/
theorem replay_artifact_read_bounded (id : String) (config : Config) (task : String)
    (records : List Lean.Json) (next : Recovery.Cursor)
    (accepted : Recovery.replay (init id config task) records = .ok next)
    (call : ToolCall) (args : ArtifactReadArgs) (operation : call.operation = .readArtifact args)
    (emitted : (step next.state).1 = .tool call) :
    (1 ≤ args.length ∧ args.length ≤ 65536) ∧
      (∃ ref ∈ next.state.artifacts, ref.id = args.id) ∧
      next.state.toolDispatches ≤ next.state.config.maxToolCalls := by
  have bounded := (replay_artifact_bounds id config task records next accepted).current call
    (emitted_tool_pending next.state call emitted)
  exact ⟨by simpa [ArtifactCallBounds, operation] using bounded,
    emitted_artifact_read_registered next.state call args operation emitted,
    (Recovery.replay_core_valid id config task records next accepted).current.budgets.2⟩

end Harness
