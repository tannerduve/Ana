import Harness.Proofs.Configuration

namespace Harness

/-- Every summary observation preserves the authoritative transcript, including
success, transient failures, malformed output, and cancellation. -/
theorem summary_history_preserved (s : State) (plan : SummaryPlan) (observation : ModelObservation) :
    (consumeSummary s plan observation).history = s.history := by
  cases observation with
  | interrupted => rfl
  | uncertain message => simp only [consumeSummary]; unfold retryOrStop; split <;> rfl
  | failure kind message =>
    cases kind <;> simp only [consumeSummary]
    all_goals first | rfl | (unfold retryOrStop; split <;> rfl)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeSummary, hs, hu, accountUsage]
    all_goals repeat' first | rfl | split | (unfold installSummary; dsimp only)

theorem summary_cancel_preserves_view (s : State) (plan : SummaryPlan) :
    (consumeSummary s plan .interrupted).activeView = s.activeView ∧
    (consumeSummary s plan .interrupted).summaries = s.summaries := by
  exact ⟨rfl, rfl⟩

theorem summary_failure_preserves_view (s : State) (plan : SummaryPlan)
    (kind : FailureClass) (message : String) :
    (consumeSummary s plan (.failure kind message)).activeView = s.activeView ∧
    (consumeSummary s plan (.failure kind message)).summaries = s.summaries := by
  cases kind <;> simp only [consumeSummary]
  all_goals first | exact ⟨rfl, rfl⟩ | (unfold retryOrStop; split <;> exact ⟨rfl, rfl⟩)

theorem installSummary_accepted (s : State) (plan : SummaryPlan) (response : ModelResponse)
    (accepted : (installSummary s plan response).phase = .controlModel) :
    installSummary s plan response = summaryCandidate s plan response ∧
    contextAdmitted (summaryCandidate s plan response) = true ∧
    historyValid (activeMessages (summaryCandidate s plan response)) = true := by
  by_cases h : (contextAdmitted (summaryCandidate s plan response) &&
      historyValid (activeMessages (summaryCandidate s plan response))) = true
  · have parts := h
    simp only [Bool.and_eq_true] at parts
    exact ⟨by simp [installSummary, h], parts.1, parts.2⟩
  · simp [installSummary, h, stop] at accepted

/-- Accepted summaries are complete, consistent responses with text and no tools. The exact
response and its source plan are retained, and the reconstructed task context is
admitted and contains paired retained tool batches under historyValid.
This establishes structure, not the factual fidelity of generated summary text. -/
theorem accepted_summary_contract (s : State) (plan : SummaryPlan) (response : ModelResponse)
    (accepted : (consumeSummary s plan (.success response)).phase = .controlModel) :
    response.stop = .endTurn ∧ ModelResponseConsistent response ∧
    response.calls.isEmpty = true ∧ response.text.isEmpty = false ∧
    response.text.utf8ByteSize ≤ s.config.maxSummaryBytes ∧
    consumeSummary s plan (.success response) = summaryCandidate (accountUsage s response.usage) plan response ∧
    contextAdmitted (summaryCandidate (accountUsage s response.usage) plan response) = true ∧
    historyValid (activeMessages (summaryCandidate (accountUsage s response.usage) plan response)) = true := by
  cases hs : response.stop with
  | endTurn =>
    cases hv : validateModelResponse response with
    | error message => simp [consumeSummary, hs, hv, stop] at accepted
    | ok value =>
      cases value
      by_cases hc : (!response.calls.isEmpty || response.text.isEmpty) = true
      · simp [consumeSummary, hs, hv, hc, stop] at accepted
      · by_cases hb : response.text.utf8ByteSize > s.config.maxSummaryBytes
        · simp [consumeSummary, hs, hv, hc, hb, stop] at accepted
        · have hi : (installSummary (accountUsage s response.usage) plan response).phase = .controlModel := by
            simpa [consumeSummary, hs, hv, hc, hb] using accepted
          obtain ⟨heq, hcontext, hpaired⟩ := installSummary_accepted _ _ _ hi
          have hcalls : response.calls.isEmpty = true ∧ response.text.isEmpty = false := by
            cases h₁ : response.calls.isEmpty <;> cases h₂ : response.text.isEmpty <;> simp_all
          exact ⟨rfl, validateModelResponse_sound response hv, hcalls.1, hcalls.2,
            Nat.le_of_not_gt hb, by simpa [consumeSummary, hs, hv, hc, hb] using heq,
            hcontext, hpaired⟩
  | toolUse => simp [consumeSummary, hs, stop] at accepted
  | maxTokens => simp [consumeSummary, hs, stop] at accepted
  | contextOverflow => simp [consumeSummary, hs, stop] at accepted
  | refusal => simp [consumeSummary, hs, stop] at accepted
  | other => simp [consumeSummary, hs, stop] at accepted

/-- The rejected completion cannot replace the active view or append an accepted
summary record. This includes summary content that fails the final size check. -/
private theorem summary_success_frame (s : State) (plan : SummaryPlan) (response : ModelResponse) :
    consumeSummary s plan (.success response) = summaryCandidate (accountUsage s response.usage) plan response ∨
    ((consumeSummary s plan (.success response)).activeView = s.activeView ∧
    (consumeSummary s plan (.success response)).summaries = s.summaries) := by
  cases hu : response.usage <;> cases hs : response.stop <;>
    simp only [consumeSummary, hs, hu, accountUsage]
  all_goals repeat' first
    | exact Or.inl rfl
    | exact Or.inr ⟨rfl, rfl⟩
    | split
    | (unfold installSummary; dsimp only)

theorem rejected_summary_preserves_view (s : State) (plan : SummaryPlan) (response : ModelResponse)
    (rejected : (consumeSummary s plan (.success response)).phase ≠ .controlModel) :
    (consumeSummary s plan (.success response)).activeView = s.activeView ∧
    (consumeSummary s plan (.success response)).summaries = s.summaries := by
  rcases summary_success_frame s plan response with installed | unchanged
  · rw [installed] at rejected
    exact False.elim (rejected rfl)
  · exact unchanged

/-- Every actual summary action has a valid frozen source plan and a bounded
request, independently of whether the generated summary will be useful. -/
theorem emitted_summary_admitted (s : State) (request : ModelRequest)
    (phase : s.phase = .summary) (emitted : (step s).fst = .model request) :
    ∃ plan, s.pendingSummary = some plan ∧ request = summaryRequest s plan ∧
      planValid s plan = true ∧ requestBytes request ≤ s.config.maxContextBytes := by
  simp only [step, phase] at emitted
  cases hp : s.pendingSummary with
  | none => simp [hp] at emitted
  | some plan =>
    simp only [hp] at emitted
    by_cases hg : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts) && planValid s plan) = true
    · simp only [hg] at emitted
      cases emitted
      simp only [Bool.and_eq_true] at hg
      have valid := hg.2
      have bound := valid
      simp only [planValid, Bool.and_eq_true, decide_eq_true_eq] at bound
      exact ⟨plan, rfl, rfl, valid, bound.2⟩
    · simp only [hg] at emitted; contradiction

/-- Summary attempts and retries reserve the same ledger used by task inference. -/
theorem admitted_summary_reservation (s : State) (plan : SummaryPlan)
    (admitted : (admitSummary s plan).phase = .summary) :
    (admitSummary s plan).modelAttempts = s.modelAttempts + 1 ∧
    (admitSummary s plan).pendingSummary = some plan ∧
    (admitSummary s plan).activeView = s.activeView := by
  unfold admitSummary at admitted ⊢
  split
  · split
    · exact ⟨rfl, rfl, rfl⟩
    · simp_all [stop]
  · simp_all [stop]

theorem task_request_preserves_instructions (s : State) :
    (modelRequest s).system = s.config.instructions := rfl

theorem summary_request_preserves_instructions (s : State) (plan : SummaryPlan) :
    (summaryRequest s plan).system = s.config.instructions := rfl

end Harness
