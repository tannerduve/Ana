import Harness.Core.ApplicationLaws
import Harness.Proofs.ApplicationCoding
import Harness.Proofs.History
import Harness.Proofs.Administrative

/-! Every emitted operation has passed its application's argument contract, both on ordinary
execution and administrative replay. This does not turn lexical paths into an IO containment proof. -/
namespace Harness
variable {app : Application} {laws : ApplicationLaws app}

theorem decoded_call_valid (laws : ApplicationLaws app) (raw : RawCall) (call : Call app)
    (accepted : decodeCall raw app = .ok call) : laws.ValidOperation call.operation := by
  by_cases empty : raw.id.isEmpty = true
  · simp [decodeCall, empty] at accepted
  · cases decoded : app.decode raw with
    | error message => simp [decodeCall, empty, decoded] at accepted
    | ok operation =>
      simp only [decodeCall, empty, decoded, ExceptRules.ok_bind, ExceptRules.pure_ok] at accepted
      cases accepted
      exact laws.decode_valid raw operation decoded

def PendingApplicationValid (laws : ApplicationLaws app) (state : State app) : Prop :=
  ∀ call ∈ pendingCalls state, laws.ValidOperation call.operation

@[simp] theorem operation_valid_advance (s : State app) : PendingApplicationValid laws (advance s) = PendingApplicationValid laws s := rfl

private theorem operation_valid_empty (s : State app) (empty : pendingCalls s = []) : PendingApplicationValid laws s := by
  simp [PendingApplicationValid, empty]

private theorem operation_valid_subqueue (s next : State app) (valid : PendingApplicationValid laws s)
    (queue : List.Sublist (pendingCalls next) (pendingCalls s)) : PendingApplicationValid laws next := by
  exact fun call member => valid call (queue.subset member)

private theorem operation_valid_admitModel (s : State app) (_valid : PendingApplicationValid laws s) : PendingApplicationValid laws (admitModel s) := by
  unfold admitModel
  repeat' first
    | (exact operation_valid_empty _ rfl)
    | split | (unfold admitTask; dsimp only) | unfold admitSummary

private theorem operation_valid_consumeModel (s : State app) (observation : ModelObservation)
    (_valid : PendingApplicationValid laws s) : PendingApplicationValid laws (consumeModel s observation) := by
  cases observation with
  | interrupted => exact operation_valid_empty _ rfl
  | uncertain message =>
    simp only [consumeModel]
    unfold retryOrStop
    split <;> exact operation_valid_empty _ rfl
  | failure kind message =>
    cases kind <;> simp only [consumeModel]
    all_goals first
      | exact operation_valid_empty _ rfl
      | exact operation_valid_empty _ (repair_pendingCalls _ _ _)
      | (unfold retryOrStop; split <;> exact operation_valid_empty _ rfl)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeModel, hs, hu, accountUsage]
    all_goals repeat' first | (exact operation_valid_empty _ rfl) | (exact operation_valid_empty _ (repair_pendingCalls _ _ _)) | (split)
    all_goals
      rename_i calls accepted
      exact validated_batch_all (fun call => laws.ValidOperation call.operation) (decoded_call_valid laws) _ _ _ _ accepted

private theorem operation_valid_consumeSummary (s : State app) (plan : SummaryPlan) (observation : ModelObservation)
    (_valid : PendingApplicationValid laws s) : PendingApplicationValid laws (consumeSummary s plan observation) := by
  cases observation with
  | interrupted => exact operation_valid_empty _ rfl
  | uncertain message =>
    simp only [consumeSummary]
    unfold retryOrStop
    split <;> exact operation_valid_empty _ rfl
  | failure kind message =>
    cases kind <;> simp only [consumeSummary]
    all_goals first
      | exact operation_valid_empty _ rfl
      | (unfold retryOrStop; split <;> exact operation_valid_empty _ rfl)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeSummary, hs, hu, accountUsage]
    all_goals repeat' first
      | (exact operation_valid_empty _ rfl)
      | split | (unfold installSummary; dsimp only)

private theorem operation_valid_admitTool (s : State app) (call : (Call app)) (remaining : List (Call app))
    (valid : PendingApplicationValid laws s) (phase : s.phase = .controlTools (call :: remaining)) :
    PendingApplicationValid laws (admitTool s call remaining) := by
  unfold admitTool
  split
  · split
    · exact operation_valid_subqueue s _ valid (by simp [pendingCalls, phase])
    · split
      · exact operation_valid_subqueue s _ valid (by simp [pendingCalls, phase])
      · exact operation_valid_subqueue s _ valid (by simp [pendingCalls, phase])
  · exact operation_valid_empty _ rfl

private theorem operation_valid_consumeTool (s : State app) (call : (Call app)) (remaining : List (Call app))
    (observation : ToolObservation ToolResult) (valid : PendingApplicationValid laws s)
    (phase : s.phase = .tool call remaining) : PendingApplicationValid laws (consumeTool s call remaining observation) := by
  have tail : ∀ proposed ∈ remaining, laws.ValidOperation proposed.operation := by
    intro proposed member
    exact valid proposed (by simp [pendingCalls, phase, member])
  cases observation <;> simp only [consumeTool, retainPartialArtifacts]
  all_goals repeat' first | (exact operation_valid_empty _ rfl) | (exact tail) | split

private theorem operation_valid_consumeApproval (s : State app) (call : (Call app)) (remaining : List (Call app))
    (observation : ApprovalObservation) (valid : PendingApplicationValid laws s)
    (phase : s.phase = .ask call remaining) : PendingApplicationValid laws (consumeApproval s call remaining observation) := by
  cases observation <;> simp only [consumeApproval]
  all_goals first
    | exact operation_valid_empty _ rfl
    | exact operation_valid_subqueue s _ valid (by simp [pendingCalls, phase])

private theorem operation_valid_controlModel (s : State app) (observation : ControlObservation) (valid : PendingApplicationValid laws s) :
    PendingApplicationValid laws (consumeControl s none observation) := by
  simp only [consumeControl]
  split
  · exact operation_valid_empty _ rfl
  · split
    · exact operation_valid_empty _ rfl
    · exact operation_valid_admitModel s valid

private theorem operation_valid_controlTools (s : State app) (calls : List (Call app)) (observation : ControlObservation)
    (valid : PendingApplicationValid laws s) (phase : s.phase = .controlTools calls) :
    PendingApplicationValid laws (consumeControl s (some calls) observation) := by
  simp only [consumeControl]
  split
  · exact operation_valid_empty _ rfl
  · split
    · exact operation_valid_empty _ rfl
    · cases calls with
      | nil => exact operation_valid_empty _ rfl
      | cons call remaining => exact operation_valid_admitTool s call remaining valid phase

private def ValidCallsNode (laws : ApplicationLaws app) (node : HarnessF app (State app)) : Prop :=
  ∀ response : Reply node.1, PendingApplicationValid laws (node.2 response)

theorem application_valid_preserved (state : State app) (valid : PendingApplicationValid laws state) :
    ∀ response : Reply (step state).1, PendingApplicationValid laws ((step state).2 response) := by
  change ValidCallsNode laws (step state)
  cases phase : state.phase <;> simp only [step, phase]
  case stopped outcome => intro response; exact response.elim
  case controlModel => exact fun response => operation_valid_controlModel state response valid
  case controlTools calls => exact fun response => operation_valid_controlTools state calls response valid phase
  case ask call remaining => exact fun response => operation_valid_consumeApproval state call remaining response valid phase
  case waiting delay =>
    intro response
    cases response <;> exact operation_valid_empty _ rfl
  case model =>
    by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts)) = true
    · erw [if_pos admitted]; exact fun response => operation_valid_consumeModel state response valid
    · erw [if_neg admitted]; intro response; exact response.elim
  case summary =>
    cases pending : state.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases admitted : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts) && planValid state plan) = true
      · erw [if_pos admitted]; exact fun response => operation_valid_consumeSummary state plan response valid
      · erw [if_neg admitted]; intro response; exact response.elim
  case tool call remaining =>
    by_cases admitted : (authorized state.config state.grant call && artifactAuthorized state call && decide (0 < state.toolDispatches) && decide (state.toolDispatches ≤ state.config.maxToolCalls)) = true
    · erw [if_pos admitted]; exact fun response => operation_valid_consumeTool state call remaining (response.map (app.render call.operation)) valid phase
    · erw [if_neg admitted]; intro response; exact response.elim


theorem reachable_application_valid {id : String} {config : Config} {task : String} {state : State app}
    (reachable : Reachable id config task state) : PendingApplicationValid laws state := by
  exact reachable.invariant (by simp [PendingApplicationValid, pendingCalls, init]) application_valid_preserved


/-- Unlike an arbitrary `State`, a reachable queue contains only admitted operations. -/
theorem emitted_operation_valid {id task : String} {config : Config} {state : State app}
    (reachable : Reachable id config task state) (call : Call app)
    (emitted : (step state).1 = .tool call) : laws.ValidOperation call.operation :=
  reachable_application_valid reachable call (emitted_tool_pending state call emitted)

private theorem applicationRecoveryRules (laws : ApplicationLaws app) :
    Recovery.RecoveryRules (PendingApplicationValid laws) where
  step := application_valid_preserved
  clearGrant := fun _ valid => valid
  approvalRetry := by
    intro state valid call remaining phase
    simpa only [PendingApplicationValid, pendingCalls, advance, phase] using valid
  userTurn := by
    intro before after task _ accepted
    rw [(begin_turn_contract before after task accepted).1]
    simp [PendingApplicationValid, pendingCalls, turnCandidate]
  artifactOverlay := fun _ _ valid _ _ _ => valid

theorem replay_application_valid (laws : ApplicationLaws app) (id : String) (config : Config)
    (task : String) (records : List Lean.Json) (next : Recovery.Cursor app)
    (accepted : Recovery.replay (init id config task app) records = .ok next) :
    Recovery.CursorProperty (PendingApplicationValid laws) next :=
  Recovery.replay_property (applicationRecoveryRules laws) (init id config task app)
    (by simp [PendingApplicationValid, pendingCalls, init]) records next accepted

theorem replay_emitted_operation_valid (laws : ApplicationLaws app) (id : String) (config : Config)
    (task : String) (records : List Lean.Json) (next : Recovery.Cursor app)
    (accepted : Recovery.replay (init id config task app) records = .ok next)
    (call : Call app) (emitted : (step next.state).1 = .tool call) :
    laws.ValidOperation call.operation :=
  (replay_application_valid laws id config task records next accepted).current call
    (emitted_tool_pending next.state call emitted)

/-- Concrete lexical path safety follows from real reachable admission, not arbitrary state. -/
theorem coding_emitted_paths_safe {id task : String} {config : Config} {state : State}
    (reachable : Reachable id config task state) (call : ToolCall)
    (emitted : (step state).1 = .tool call) :
    ∀ path ∈ Coding.operationPaths call.operation, Coding.safePath path = true :=
  Coding.valid_operation_paths call.operation (emitted_operation_valid (laws := Coding.laws) reachable call emitted)

/-- This also covers accepted administrative recovery and follow-up records. Physical
filesystem containment remains the adapter contract, not a consequence of lexical checking. -/
theorem coding_replay_emitted_paths_safe (id : String) (config : Config) (task : String)
    (records : List Lean.Json) (next : Recovery.Cursor)
    (accepted : Recovery.replay (init id config task) records = .ok next)
    (call : ToolCall) (emitted : (step next.state).1 = .tool call) :
    ∀ path ∈ Coding.operationPaths call.operation, Coding.safePath path = true :=
  Coding.valid_operation_paths call.operation
    (replay_emitted_operation_valid Coding.laws id config task records next accepted call emitted)

end Harness
