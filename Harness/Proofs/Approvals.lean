import Harness.Proofs.Configuration
import Harness.Proofs.Trace
import Harness.Proofs.Recovery

/-! Approval provenance for executable transitions. The trusted input is an
`ApprovalObservation.approved` reply, never a string supplied by the model. IO
prompt delivery and operator identity remain interpreter obligations. -/
namespace Harness

variable {app : Application}

/-- Extract only the typed approval reply to an ask for this exact call. -/
def approvedCall : (action : (Action app)) → Reply action → Option (Call app)
  | .ask call, .approved => some call
  | _, _ => none

private theorem grant_model (s : (State app)) (observation : ModelObservation) :
    (consumeModel s observation).grant = none ∨ (consumeModel s observation).grant = s.grant := by
  cases observation with
  | interrupted => simp [consumeModel, stop]
  | uncertain message => simp only [consumeModel]; unfold retryOrStop; split <;> simp [stop]
  | failure kind message =>
    cases kind <;> simp only [consumeModel]
    all_goals repeat' first | (solve | simp [stop]) | (unfold retryOrStop; split)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeModel, hs, hu, accountUsage]
    all_goals repeat' first | (solve | simp [stop]) | split

private theorem grant_summary (s : (State app)) (plan : SummaryPlan) (observation : ModelObservation) :
    (consumeSummary s plan observation).grant = none ∨ (consumeSummary s plan observation).grant = s.grant := by
  cases observation with
  | interrupted => simp [consumeSummary, stop]
  | uncertain message => simp only [consumeSummary]; unfold retryOrStop; split <;> simp [stop]
  | failure kind message =>
    cases kind <;> simp only [consumeSummary]
    all_goals repeat' first | (solve | simp [stop]) | (unfold retryOrStop; split)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeSummary, hs, hu, accountUsage]
    all_goals repeat' first | (solve | simp [stop, summaryCandidate]) | split | (unfold installSummary; dsimp only)

private theorem grant_admitModel (s : (State app)) :
    (admitModel s).grant = none ∨ (admitModel s).grant = s.grant := by
  unfold admitModel
  repeat' first | (solve | simp [stop]) | split | (unfold admitTask; dsimp only) | unfold admitSummary

private theorem grant_control (s : (State app)) (calls : Option (List (Call app))) (observation : ControlObservation) :
    (consumeControl s calls observation).grant = none ∨ (consumeControl s calls observation).grant = s.grant := by
  unfold consumeControl
  split
  · simp [cancelCalls]
  · split
    · simp [stop]
    · cases calls with
      | none => exact grant_admitModel s
      | some calls =>
        cases calls with
        | nil => simp
        | cons call rest =>
          dsimp only
          unfold admitTool
          repeat' first | (solve | simp [stop, appendResult]) | split

/-- Any typed tool reply consumes the one-operation grant, including uncertainty
and interruption. A continuation cannot use that grant for a second dispatch. -/
theorem tool_reply_clears_grant (s : (State app)) (call : (Call app)) (remaining : List (Call app))
    (observation : ToolObservation ToolResult) :
    (consumeTool s call remaining observation).grant = none := by
  cases observation <;> simp only [consumeTool]
  all_goals repeat' first | (solve | simp [stop, appendResult, settleTimedOut]) | split

private def ApprovalNode (s : (State app)) (node : (HarnessF app) (State app)) : Prop :=
  ∀ (reply : Reply node.fst) (call : (Call app)),
    (node.snd reply).grant = some call →
      s.grant = some call ∨ approvedCall node.fst reply = some call

/-- Typed model/tool/control replies cannot manufacture an approval. A newly
introduced grant comes only from an approved ask for the entire exact (Call app). -/
theorem grant_step_source (s : (State app)) :
    ∀ (reply : Reply (step s).fst) (call : (Call app)),
    ((step s).snd reply).grant = some call →
      s.grant = some call ∨ approvedCall (step s).fst reply = some call := by
  change ApprovalNode s (step s)
  cases hp : s.phase <;> simp only [step, hp]
  case stopped outcome => intro reply; exact reply.elim
  case controlModel =>
    intro reply call present
    rcases grant_control s none reply with clear | preserved
    · simp [advance, clear] at present
    · exact Or.inl (preserved.symm.trans present)
  case controlTools calls =>
    intro reply call present
    rcases grant_control s (some calls) reply with clear | preserved
    · simp [advance, clear] at present
    · exact Or.inl (preserved.symm.trans present)
  case ask proposed remaining =>
    intro reply call present
    cases reply <;> simp [advance, consumeApproval, cancelCalls, appendResult] at present
    subst call
    exact Or.inr rfl
  case waiting delay =>
    intro reply call present
    cases reply with
    | elapsed => exact Or.inl present
    | interrupted => simp [advance, consumeWait, stop] at present
  case model =>
    by_cases allowed : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts)) = true
    · erw [if_pos allowed]
      intro reply call present
      rcases grant_model s reply with clear | preserved
      · simp [advance, clear] at present
      · exact Or.inl (preserved.symm.trans present)
    · erw [if_neg allowed]; intro reply; exact reply.elim
  case summary =>
    cases pending : s.pendingSummary with
    | none => intro reply; exact reply.elim
    | some plan =>
      dsimp only
      by_cases allowed : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts) && planValid s plan) = true
      · erw [if_pos allowed]
        intro reply call present
        rcases grant_summary s plan reply with clear | preserved
        · simp [advance, clear] at present
        · exact Or.inl (preserved.symm.trans present)
      · erw [if_neg allowed]; intro reply; exact reply.elim
  case tool call remaining =>
    by_cases allowed : (authorized s.config s.grant call && artifactAuthorized s call && decide (0 < s.toolDispatches) && decide (s.toolDispatches ≤ s.config.maxToolCalls)) = true
    · erw [if_pos allowed]
      intro reply proposed present
      simp [advance, tool_reply_clears_grant] at present
    · erw [if_neg allowed]; intro reply; exact reply.elim

/-- This is equality of the typed call, including call identity, argv and cwd.
The frozen session configuration separately binds workspace and permission policy. -/
theorem emitted_ask_tool_requires_exact_grant (s : (State app)) (call : (Call app))
    (emitted : (step s).fst = .tool call) (asked : policy s.config call = .ask) :
    s.grant = some call := by
  have permitted := emitted_tool_authorized s call emitted
  simpa [authorized, asked] using permitted

/-- A witnessed event in an actual executable trace, including its prefix and
suffix. This is a proof relation, not an extra serialized grant field. -/
def ApprovalIn (first last : (State app)) (events : List (ObservedStep app)) (call : (Call app)) : Prop :=
  ∃ (before after : List (ObservedStep app)) (approvedState : (State app))
      (reply : Reply (step approvedState).fst),
    events = before ++ observe approvedState reply :: after ∧
    ExecutionTrace first before approvedState ∧
    approvedCall (step approvedState).fst reply = some call ∧
    ExecutionTrace ((step approvedState).snd reply) after last

/-- A grant present at the end of a finite trace either existed at its start or
has a typed approval event in that trace. Model content cannot supply this event. -/
theorem ExecutionTrace.grant_source {first last : (State app)} {events : List (ObservedStep app)}
    (trace : ExecutionTrace first events last) :
    ∀ call, last.grant = some call → first.grant = some call ∨ ApprovalIn first last events call := by
  induction trace with
  | nil state => intro call present; exact Or.inl present
  | cons state response tail ih =>
    intro call present
    rcases ih call present with previous | origin
    · rcases grant_step_source state response call previous with inherited | approved
      · exact Or.inl inherited
      · exact Or.inr ⟨[], _, state, response, rfl, .nil _, approved, tail⟩
    · obtain ⟨before, after, approvedState, reply, equality, prefixTrace, approval, suffix⟩ := origin
      exact Or.inr ⟨observe state response :: before, after, approvedState, reply,
        by simp [equality], .cons state response prefixTrace, approval, suffix⟩

theorem approvedCall_trusted {action : (Action app)} {reply : Reply action} {call : (Call app)}
    (approved : approvedCall action reply = some call) :
    action = .ask call ∧ HEq reply ApprovalObservation.approved := by
  cases action <;> simp only [approvedCall] at approved
  all_goals try contradiction
  case ask proposed =>
    cases reply
    all_goals try contradiction
    cases approved
    exact ⟨rfl, HEq.rfl⟩

/-- An ask-policy dispatch in a trace from initialization has an earlier trusted
approval for the exact typed call. Both the approved state and dispatch retain the
initial full configuration (workspace, policy, isolation, provider and limits). -/
theorem execution_tool_has_trusted_approval {id : String} {config : Config} {task : String}
    {state : (State app)} {events : List (ObservedStep app)} (call : (Call app))
    (trace : ExecutionTrace (init id config task app) events state)
    (emitted : (step state).fst = .tool call) (asked : policy config call = .ask) :
    ∃ (before after : List (ObservedStep app)) (approvedState : (State app))
        (reply : Reply (step approvedState).fst),
      events = before ++ observe approvedState reply :: after ∧
      ExecutionTrace (init id config task app) before approvedState ∧
      ExecutionTrace ((step approvedState).snd reply) after state ∧
      (step approvedState).fst = .ask call ∧ HEq reply ApprovalObservation.approved ∧
      approvedState.config = config ∧ state.config = config := by
  have frozen : state.config = config := reachable_config (trace.reachable .initial)
  have grant := emitted_ask_tool_requires_exact_grant state call emitted (by simpa [frozen] using asked)
  rcases trace.grant_source call grant with initialGrant | origin
  · simp [init] at initialGrant
  · obtain ⟨before, after, approvedState, reply, equality, prefixTrace, approval, suffix⟩ := origin
    obtain ⟨action, trusted⟩ := approvedCall_trusted approval
    exact ⟨before, after, approvedState, reply, equality, prefixTrace, suffix, action, trusted,
      reachable_config (prefixTrace.reachable .initial), frozen⟩

private def ToolClearNode (node : (HarnessF app) (State app)) : Prop :=
  ∀ (reply : Reply node.fst) (call : (Call app)), node.fst = .tool call → (node.snd reply).grant = none

/-- This statement applies to the actual continuation returned for an emitted
request, rather than to a separately chosen tool transition. -/
theorem emitted_tool_reply_clears_grant (state : (State app)) :
    ∀ (reply : Reply (step state).fst) (call : (Call app)),
      (step state).fst = .tool call → ((step state).snd reply).grant = none := by
  change ToolClearNode (step state)
  cases phase : state.phase <;> simp only [step, phase]
  case stopped outcome => intro reply; exact reply.elim
  case controlModel => simp [ToolClearNode]
  case controlTools calls => simp [ToolClearNode]
  case ask call remaining => simp [ToolClearNode]
  case waiting delay => simp [ToolClearNode]
  case model =>
    by_cases allowed : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts)) = true
    · erw [if_pos allowed]; simp [ToolClearNode]
    · erw [if_neg allowed]; intro reply; exact reply.elim
  case summary =>
    cases pending : state.pendingSummary with
    | none => intro reply; exact reply.elim
    | some plan =>
      dsimp only
      by_cases allowed : (decide (0 < state.modelAttempts) && decide (state.modelAttempts ≤ state.config.maxModelAttempts) && planValid state plan) = true
      · erw [if_pos allowed]; simp [ToolClearNode]
      · erw [if_neg allowed]; intro reply; exact reply.elim
  case tool call remaining =>
    by_cases allowed : (authorized state.config state.grant call && artifactAuthorized state call && decide (0 < state.toolDispatches) && decide (state.toolDispatches ≤ state.config.maxToolCalls)) = true
    · erw [if_pos allowed]
      intro reply proposed emitted
      exact tool_reply_clears_grant state call remaining (reply.map (app.render call.operation))
    · erw [if_neg allowed]; intro reply; exact reply.elim

/-- Any second ask-policy dispatch needs a fresh approved event after the first
request's reply. One grant cannot authorize two dispatched interactions, even when
the second call has exactly the same arguments and identity as the first. -/
theorem next_dispatch_needs_fresh_approval {first last : (State app)} (firstCall nextCall : (Call app))
    (reply : Reply (step first).fst) {events : List (ObservedStep app)}
    (firstEmitted : (step first).fst = .tool firstCall)
    (trace : ExecutionTrace ((step first).snd reply) events last)
    (nextEmitted : (step last).fst = .tool nextCall) (asked : policy last.config nextCall = .ask) :
    ApprovalIn ((step first).snd reply) last events nextCall := by
  have cleared := emitted_tool_reply_clears_grant first reply firstCall firstEmitted
  have grant := emitted_ask_tool_requires_exact_grant last nextCall nextEmitted asked
  rcases trace.grant_source nextCall grant with old | fresh
  · simp [cleared] at old
  · exact fresh

/-- Losing an approval cannot restore its answer from the prior cursor. A later
ask-policy dispatch after this administrative reset requires an approval in the
new ordinary trace. This does not claim a theorem for arbitrary mixed replay. -/
theorem lost_approval_needs_new_approval (cursor : Recovery.Cursor app) (prior : (State app))
    (call : (Call app)) (remaining : List (Call app)) (next : Recovery.Cursor app)
    (target : Recovery.checkedTarget cursor = .ok prior) (phase : prior.phase = .ask call remaining)
    (recovered : Recovery.recover cursor prior.nextId .approvalLost = .ok next)
    {events : List (ObservedStep app)} {last : (State app)}
    (trace : ExecutionTrace next.state events last) (proposed : (Call app))
    (emitted : (step last).fst = .tool proposed) (asked : policy last.config proposed = .ask) :
    ApprovalIn next.state last events proposed := by
  rw [Recovery.recover_approval_lost cursor prior call remaining target phase] at recovered
  cases recovered
  have grant := emitted_ask_tool_requires_exact_grant last proposed emitted asked
  rcases trace.grant_source proposed grant with old | fresh
  · simp [advance] at old
  · exact fresh

/-- A restart at a control boundary revokes even a previously persisted approval;
its later ask-policy dispatch must be justified by a new trusted reply. -/
theorem lost_control_needs_new_approval (cursor : Recovery.Cursor app) (prior : (State app))
    (next : Recovery.Cursor app) (target : Recovery.checkedTarget cursor = .ok prior)
    (control : (step prior).fst = .control)
    (recovered : Recovery.recover cursor prior.nextId .controlLost = .ok next)
    {events : List (ObservedStep app)} {last : (State app)}
    (trace : ExecutionTrace next.state events last) (proposed : (Call app))
    (emitted : (step last).fst = .tool proposed) (asked : policy last.config proposed = .ask) :
    ApprovalIn next.state last events proposed := by
  rw [Recovery.recover_control_lost cursor prior target control] at recovered
  cases recovered
  have grant := emitted_ask_tool_requires_exact_grant last proposed emitted asked
  rcases trace.grant_source proposed grant with old | fresh
  · simp [advance] at old
  · exact fresh

end Harness
