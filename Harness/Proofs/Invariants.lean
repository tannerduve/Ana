import Harness.Proofs.ResponseRepair
import Harness.Proofs.Reachability

namespace Harness

variable {app : Application}


/-- The initial invariant concerns hard dispatch ceilings. History and OS obligations
    are tested separately; this predicate makes no stronger claim about them. -/
def BudgetValid (s : (State app)) : Prop :=
  s.modelAttempts ≤ s.config.maxModelAttempts ∧ s.toolDispatches ≤ s.config.maxToolCalls

@[simp] theorem budget_init (id : String) (cfg : Config) (task : String) :
    BudgetValid (init id cfg task app) := by
  simp [BudgetValid, init]

@[simp] theorem budget_advance (s : (State app)) : BudgetValid (advance s) = BudgetValid s := rfl
@[simp] theorem budget_stop (s : (State app)) (o : Outcome) : BudgetValid (stop s o) = BudgetValid s := rfl
@[simp] theorem budget_appendResult (s : (State app)) (c : (Call app)) (t : String) (b : Bool) :
    BudgetValid (appendResult s c t b) = BudgetValid s := rfl

 theorem budget_admitTask (s : (State app)) (h : BudgetValid s) : BudgetValid (admitTask s) := by
  unfold admitTask
  dsimp only
  split
  · split
    · split
      · simp only [BudgetValid] at *
        constructor <;> omega
      · exact h
    · exact h
  · exact h

 theorem budget_admitSummary (s : (State app)) (plan : SummaryPlan) (h : BudgetValid s) :
    BudgetValid (admitSummary s plan) := by
  unfold admitSummary
  split
  · split
    · simp only [BudgetValid] at *
      constructor <;> omega
    · exact h
  · exact h

 theorem budget_admitModel (s : (State app)) (h : BudgetValid s) : BudgetValid (admitModel s) := by
  unfold admitModel
  split
  · exact budget_admitSummary _ _ h
  · split
    · split
      · exact budget_admitSummary _ _ h
      · exact budget_admitTask _ h
    · exact budget_admitTask _ h

 theorem budget_admitTool (s : (State app)) (c : (Call app)) (rest : List (Call app))
    (h : BudgetValid s) : BudgetValid (admitTool s c rest) := by
  unfold admitTool
  split
  · split
    · simp only [BudgetValid] at *
      constructor <;> omega
    · split <;> exact h
  · exact h

 theorem budget_consumeControl (s : (State app)) (calls : Option (List (Call app))) (o : ControlObservation)
    (h : BudgetValid s) : BudgetValid (consumeControl s calls o) := by
  unfold consumeControl
  split
  · exact h
  · split
    · exact h
    · cases calls with
      | none => exact budget_admitModel s h
      | some calls => cases calls with
        | nil => exact h
        | cons c rest => exact budget_admitTool s c rest h

 theorem budget_consumeModel (s : (State app)) (o : ModelObservation) (h : BudgetValid s) :
    BudgetValid (consumeModel s o) := by
  unfold BudgetValid at *
  cases o with
  | interrupted => exact h
  | uncertain m => simp only [consumeModel]; unfold retryOrStop; split <;> exact h
  | failure k m =>
    cases k <;> simp only [consumeModel]
    all_goals first | exact h | (simpa only [repair_modelAttempts, repair_toolDispatches, repair_config] using h) | (unfold retryOrStop; split <;> exact h)
  | success r =>
    cases hu : r.usage <;> cases hs : r.stop <;>
      simp only [consumeModel, hs, hu, accountUsage]
    all_goals repeat' first | exact h | (simpa only [repair_modelAttempts, repair_toolDispatches, repair_config] using h) | split

 theorem budget_installSummary (s : (State app)) (plan : SummaryPlan) (response : ModelResponse)
    (h : BudgetValid s) : BudgetValid (installSummary s plan response) := by
  unfold installSummary
  dsimp only
  split <;> exact h

 theorem budget_consumeSummary (s : (State app)) (plan : SummaryPlan) (o : ModelObservation)
    (h : BudgetValid s) : BudgetValid (consumeSummary s plan o) := by
  cases o with
  | interrupted => exact h
  | uncertain m => simp only [consumeSummary]; unfold retryOrStop; split <;> exact h
  | failure k m =>
    cases k <;> simp only [consumeSummary]
    all_goals first | exact h | (unfold retryOrStop; split <;> exact h)
  | success r =>
    cases hu : r.usage <;> cases hs : r.stop <;>
      simp only [consumeSummary, hs, hu, accountUsage]
    all_goals repeat' first | exact h | exact budget_installSummary _ _ _ h | split

 theorem budget_consumeTool (s : (State app)) (c : (Call app)) (rest : List (Call app))
    (o : ToolObservation ToolResult) (h : BudgetValid s) :
    BudgetValid (consumeTool s c rest o) := by
  cases o <;> simp only [consumeTool, retainPartialArtifacts]
  all_goals repeat' first | exact h | split

 theorem budget_consumeApproval (s : (State app)) (c : (Call app)) (rest : List (Call app))
    (o : ApprovalObservation) (h : BudgetValid s) :
    BudgetValid (consumeApproval s c rest o) := by
  cases o <;> exact h

 theorem budget_consumeWait (s : (State app)) (o : WaitObservation) (h : BudgetValid s) :
    BudgetValid (consumeWait s o) := by
  cases o <;> exact h

/-- A predicate on the polynomial-functor object keeps dependent replies together. -/
def BudgetNode (node : (HarnessF app) (State app)) : Prop :=
  ∀ r : Reply node.fst, BudgetValid (node.snd r)

/-- Every typed coalgebra continuation preserves the dispatch ceilings. -/
theorem budget_preserved (s : (State app)) (h : BudgetValid s) :
    ∀ r : Reply (step s).fst, BudgetValid ((step s).snd r) := by
  change BudgetNode (step s)
  cases hp : s.phase <;> simp only [step, hp]
  case stopped o => intro r; exact r.elim
  case controlModel => exact fun r => budget_consumeControl _ none r h
  case controlTools calls => exact fun r => budget_consumeControl _ (some calls) r h
  case ask c rest => exact fun r => budget_consumeApproval _ c rest r h
  case waiting ms => exact fun r => budget_consumeWait _ r h
  case model =>
    by_cases hg : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts)) = true
    · erw [if_pos hg]; exact fun r => budget_consumeModel _ r h
    · erw [if_neg hg]; intro r; exact r.elim
  case summary =>
    cases hpending : s.pendingSummary with
    | none => intro r; exact r.elim
    | some plan =>
      dsimp only
      by_cases hg : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts) && planValid s plan) = true
      · erw [if_pos hg]; exact fun r => budget_consumeSummary _ plan r h
      · erw [if_neg hg]; intro r; exact r.elim
  case tool c rest =>
    by_cases hg : (authorized s.config s.grant c && artifactAuthorized s c && decide (0 < s.toolDispatches) && decide (s.toolDispatches ≤ s.config.maxToolCalls)) = true
    · erw [if_pos hg]; exact fun r => budget_consumeTool _ c rest (r.map (app.render c.operation)) h
    · erw [if_neg hg]; intro r; exact r.elim

/-- Dispatch checks authorization again even for a forged serialized phase. -/
theorem emitted_tool_authorized (s : (State app)) (c : (Call app))
    (h : (step s).fst = .tool c) : authorized s.config s.grant c = true := by
  cases hp : s.phase <;> simp only [step, hp] at h
  all_goals try contradiction
  case model =>
    by_cases hg : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts)) = true
    · simp only [hg] at h; contradiction
    · simp only [hg] at h; contradiction
  case summary =>
    cases hpending : s.pendingSummary with
    | none => simp [hpending] at h
    | some plan =>
      simp only [hpending] at h
      by_cases hg : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts) && planValid s plan) = true
      · simp only [hg] at h; contradiction
      · simp only [hg] at h; contradiction
  case tool call rest =>
    by_cases hg : (authorized s.config s.grant call && artifactAuthorized s call && decide (0 < s.toolDispatches) && decide (s.toolDispatches ≤ s.config.maxToolCalls)) = true
    · simp only [hg] at h
      cases h
      simp only [Bool.and_eq_true] at hg
      exact hg.1.1.1
    · simp only [hg] at h; contradiction

 theorem terminal_action (s : (State app)) (o : Outcome) (h : s.phase = .stopped o) :
    (step s).fst = .finish o := by simp [step, h]

 theorem cancellation_terminal (s : (State app)) (calls : Option (List (Call app))) (o : ControlObservation)
    (h : o.cancelled = true) :
    (step (advance (consumeControl s calls o))).fst = .finish .cancelled := by
  simp [consumeControl, h, advance, step, cancelCalls]


 theorem changed_grant_unusable (cfg : Config) (granted proposed : (Call app))
    (hp : policy cfg proposed = .ask) (different : granted ≠ proposed) :
    authorized cfg (some granted) proposed = false := by
  simp [authorized, hp, different]

 theorem reachable_budgets {id : String} {cfg : Config} {task : String} {s : (State app)}
    (h : Reachable id cfg task s) : BudgetValid s :=
  h.invariant (budget_init _ _ _) budget_preserved

/-- Successful validation connects retained content to all normalized call descriptors
and to the final text. No injectivity theorem about JSON serialization is assumed. -/
theorem validateModelResponse_sound (response : ModelResponse)
    (h : validateModelResponse response = .ok ()) : ModelResponseConsistent response := by
  cases hp : parseModelContent response.content with
  | error message => simp [validateModelResponse, hp] at h
  | ok decoded =>
    rcases decoded with ⟨calls, text⟩
    by_cases hc : calls.map RawCall.descriptor = response.calls.map RawCall.descriptor
    · by_cases ht : text = response.text
      · exact ⟨(calls, text), hp, hc, ht⟩
      · simp [validateModelResponse, hp, hc, ht] at h
    · simp [validateModelResponse, hp, hc] at h

/-- A rejected complete response retains the whole prior logical state except its
accounted usage, terminal failure, and cleared grant. In particular it cannot append
history, admit calls, or spend an additional dispatch reservation. -/
theorem rejected_model_response_state (s : (State app)) (response : ModelResponse) (message : String)
    (hstop : response.stop = .endTurn ∨ response.stop = .toolUse)
    (h : validateModelResponse response = .error message) :
    consumeModel s (.success response) =
      stop (accountUsage s response.usage) (.failure s!"invalid model response: {message}") := by
  rcases hstop with hs | hs <;> simp [consumeModel, hs, h]

/-- Logical inconsistency or malformed supported content cannot be accepted merely
because an adapter or journal supplied an inhabitant of ModelResponse. -/
theorem inconsistent_model_response_stops (s : (State app)) (response : ModelResponse)
    (hstop : response.stop = .endTurn ∨ response.stop = .toolUse)
    (hinconsistent : ¬ ModelResponseConsistent response) :
    ∃ message, consumeModel s (.success response) =
      stop (accountUsage s response.usage) (.failure message) := by
  cases hv : validateModelResponse response with
  | error message =>
    exact ⟨s!"invalid model response: {message}", rejected_model_response_state s response message hstop hv⟩
  | ok result =>
    cases result
    exact False.elim (hinconsistent (validateModelResponse_sound response hv))

@[simp] theorem accountUsage_config (s : (State app)) (usage : Option Usage) :
    (accountUsage s usage).config = s.config := by cases usage <;> rfl

@[simp] theorem accountUsage_history (s : (State app)) (usage : Option Usage) :
    (accountUsage s usage).history = s.history := by cases usage <;> rfl

@[simp] theorem accountUsage_seenCallIds (s : (State app)) (usage : Option Usage) :
    (accountUsage s usage).seenCallIds = s.seenCallIds := by cases usage <;> rfl

/-- Every newly admitted tool batch is decoded from a response whose retained
content agrees with its ordered call descriptors/text. The actual pending calls
are the successfully validated batch, and the exact original blocks enter history. -/
theorem accepted_tool_response_contract (s : (State app)) (response : ModelResponse) (calls : List (Call app))
    (accepted : (consumeModel s (.success response)).phase = .controlTools calls) :
    response.stop = .toolUse ∧ ModelResponseConsistent response ∧
    validateBatch s.config s.seenCallIds response.calls app = .ok calls ∧
    (consumeModel s (.success response)).history =
      s.history ++ [{role := "assistant", content := response.content}] := by
  cases hs : response.stop with
  | endTurn =>
    cases hv : validateModelResponse response with
    | error message => simp [consumeModel, hs, hv, stop] at accepted
    | ok result =>
      cases result
      by_cases he : response.calls.isEmpty = true <;>
        simp [consumeModel, hs, hv, he, stop] at accepted
  | toolUse =>
    cases hv : validateModelResponse response with
    | error message => simp [consumeModel, hs, hv, stop] at accepted
    | ok result =>
      cases result
      cases hb : validateBatch s.config s.seenCallIds response.calls app with
      | error message => simp [consumeModel, hs, hv, hb] at accepted
      | ok admitted =>
        have hc : admitted = calls := by
          simpa [consumeModel, hs, hv, hb] using accepted
        subst admitted
        exact ⟨rfl, validateModelResponse_sound response hv, rfl, by simp [consumeModel, hs, hv, hb]⟩
  | maxTokens => simp [consumeModel, hs] at accepted
  | contextOverflow => simp [consumeModel, hs, stop] at accepted
  | refusal => simp [consumeModel, hs, stop] at accepted
  | other => simp [consumeModel, hs, stop] at accepted

/-- The rejection is terminal in the executable coalgebra after observation
consumption, rather than a repair path that could launch another model or tool. -/
theorem inconsistent_model_response_terminal (s : (State app)) (response : ModelResponse)
    (hstop : response.stop = .endTurn ∨ response.stop = .toolUse)
    (hinconsistent : ¬ ModelResponseConsistent response) :
    ∃ message, (step (advance (consumeModel s (.success response)))).fst = .finish (.failure message) := by
  obtain ⟨message, hs⟩ := inconsistent_model_response_stops s response hstop hinconsistent
  exact ⟨message, by simp [hs, advance, stop, step]⟩

/-- The common session policy is a ceiling: no application can override deny. -/
theorem global_tool_denied (cfg : Config) (grant : Option (Call app)) (call : Call app)
    (denied : cfg.toolPolicy = .deny) : authorized cfg grant call = false := by
  simp [authorized, policy, approvalPolicy, denied]

/-- An emitted operation is authorized by the same frozen session-wide ceiling. -/
theorem emitted_tool_global_policy_not_denied (state : State app) (call : Call app)
    (emitted : (step state).1 = .tool call) : state.config.toolPolicy ≠ .deny := by
  intro denied
  have allowed := emitted_tool_authorized state call emitted
  simp [global_tool_denied state.config state.grant call denied] at allowed

end Harness
