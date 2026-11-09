import Harness.Proofs.Except
import Harness.Proofs.Trace
import Harness.Proofs.Configuration
import Harness.Core.Recovery

/-! These statements concern the executable core's metadata registry. They do not
prove that a stored blob exists, matches its digest, or survived a filesystem flush.
Ordinary execution traces and administrative recovery are scoped separately. -/
namespace Harness

variable {app : Application}

open ExceptRules

def ArtifactRegistryValid (config : Config) (refs : List ArtifactRef) : Prop :=
  (∀ ref ∈ refs, artifactRefValid config ref = true) ∧
  refs.length ≤ 1024 ∧ artifactBytes refs ≤ config.maxSessionArtifactBytes ∧
  (refs.map (·.id)).Nodup

def ArtifactsValid (state : (State app)) : Prop :=
  ArtifactRegistryValid state.config state.artifacts

private def registerOne (config : Config) (refs : List ArtifactRef)
    (ref : ArtifactRef) : Except String (List ArtifactRef) := do
  unless artifactRefValid config ref do throw "invalid artifact metadata"
  match refs.find? (fun item => item.id == ref.id) with
  | some prior => if prior == ref then pure refs else throw "artifact identity changed"
  | none =>
    if refs.length ≥ 1024 || artifactBytes refs + ref.storedBytes > config.maxSessionArtifactBytes then
      throw "session artifact allowance exhausted"
    return refs ++ [ref]

private theorem registerOne_contract (config : Config) (before after : List ArtifactRef)
    (ref : ArtifactRef) (valid : ArtifactRegistryValid config before)
    (accepted : registerOne config before ref = .ok after) :
    before <+: after ∧ ArtifactRegistryValid config after := by
  by_cases hv : artifactRefValid config ref = true
  · cases hf : before.find? (fun item => item.id == ref.id) with
    | some prior =>
      by_cases he : (prior == ref) = true
      · have eq : before = after := by simpa [registerOne, hv, hf, he] using accepted
        subst after
        exact ⟨by simp, valid⟩
      · simp [registerOne, hv, hf, he] at accepted
    | none =>
      by_cases hb : before.length ≥ 1024 || artifactBytes before + ref.storedBytes > config.maxSessionArtifactBytes
      · simp [registerOne, hv, hf, hb] at accepted
      · have eq : before ++ [ref] = after := by simpa [registerOne, hv, hf, hb] using accepted
        subst after
        refine ⟨List.prefix_append _ _, ?_⟩
        obtain ⟨hm, hl, hbytes, huniq⟩ := valid
        have bounds : before.length < 1024 ∧ artifactBytes before + ref.storedBytes ≤ config.maxSessionArtifactBytes := by
          simpa only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le, Nat.not_lt] using hb
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro item member
          rcases List.mem_append.mp member with prior | added
          · exact hm _ prior
          · simpa using (List.mem_singleton.mp added ▸ hv)
        · simp only [List.length_append, List.length_singleton]; omega
        · simpa [artifactBytes, List.map_append, List.sum_append] using bounds.2
        · simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append,
            List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, true_and]
          refine ⟨huniq, ?_⟩
          intro id mem other singleton
          have hs : other = ref.id := List.mem_singleton.mp singleton
          subst other
          obtain ⟨item, hi, rfl⟩ := List.mem_map.mp mem
          have absent := List.find?_eq_none.mp hf item hi
          simpa using absent
  · simp [registerOne, hv] at accepted

private theorem fold_registration_contract (config : Config) (offered : List ArtifactRef)
    (before after : List ArtifactRef) (valid : ArtifactRegistryValid config before)
    (accepted : offered.foldlM (registerOne config) before = .ok after) :
    before <+: after ∧ ArtifactRegistryValid config after := by
  induction offered generalizing before with
  | nil =>
    have eq : before = after := by simpa using accepted
    subst after
    exact ⟨by simp, valid⟩
  | cons ref rest ih =>
    cases hm : registerOne config before ref with
    | error message => simp [List.foldlM_cons, hm] at accepted
    | ok middle =>
      obtain ⟨headPrefix, middleValid⟩ := registerOne_contract config before middle ref valid hm
      have tail : rest.foldlM (registerOne config) middle = .ok after := by
        simpa [List.foldlM_cons, hm] using accepted
      obtain ⟨tailPrefix, afterValid⟩ := ih middle middleValid tail
      exact ⟨headPrefix.trans tailPrefix, afterValid⟩

/-- Accepted batches append immutable identities, preserve unique IDs, and respect
the metadata count and retained-byte ledger bounds. -/
theorem registerArtifacts_contract (config : Config) (before after : List ArtifactRef)
    (offered : Array ArtifactRef) (valid : ArtifactRegistryValid config before)
    (accepted : registerArtifacts config before offered = .ok after) :
    before <+: after ∧ ArtifactRegistryValid config after := by
  by_cases count : offered.size > 2
  · simp [registerArtifacts, count] at accepted
  · have equation : registerArtifacts config before offered = offered.foldlM (registerOne config) before := by
      simp only [registerArtifacts, count, ↓reduceIte, pure_ok]
      apply congrArg (fun operation => offered.foldlM operation before)
      funext refs ref
      by_cases hv : artifactRefValid config ref = true
      · cases hf : refs.find? (fun item => item.id == ref.id) <;>
          simp [registerOne, hv, hf]
      · simp [registerOne, hv]
    rw [equation] at accepted
    have folded : offered.toList.foldlM (registerOne config) before = .ok after := by
      simpa only [Array.foldlM_toList] using accepted
    exact fold_registration_contract config offered.toList before after valid folded

private def RegistryChange (before after : (State app)) : Prop :=
  after.artifacts = before.artifacts ∨
  ∃ offered, registerArtifacts before.config before.artifacts offered = .ok after.artifacts

private theorem artifacts_consumeModel (s : (State app)) (observation : ModelObservation) :
    (consumeModel s observation).artifacts = s.artifacts := by
  cases observation with
  | interrupted => rfl
  | uncertain message => simp only [consumeModel]; unfold retryOrStop; split <;> rfl
  | failure kind message =>
    cases kind <;> simp only [consumeModel]
    all_goals first | rfl | (solve | simp only [repair_artifacts]) | (unfold retryOrStop; split <;> rfl)
  | success response =>
    cases hu : response.usage <;> cases hs : response.stop <;>
      simp only [consumeModel, hs, hu, accountUsage]
    all_goals repeat' first | rfl | (solve | simp only [repair_artifacts]) | split

/-- Compaction cannot remove or alter admitted artifact identities. -/
theorem summary_artifacts_preserved (s : (State app)) (plan : SummaryPlan) (observation : ModelObservation) :
    (consumeSummary s plan observation).artifacts = s.artifacts := by
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

private theorem artifacts_consumeControl (s : (State app)) (calls : Option (List (Call app)))
    (observation : ControlObservation) : (consumeControl s calls observation).artifacts = s.artifacts := by
  simp only [consumeControl]
  repeat' first | rfl | split | (unfold admitModel) | (unfold admitTask; dsimp only) |
    (unfold admitSummary) | (unfold admitTool)

private theorem artifacts_consumeTool (s : (State app)) (call : (Call app)) (rest : List (Call app))
    (observation : ToolObservation ToolResult) : RegistryChange s (consumeTool s call rest observation) := by
  cases observation <;> simp only [RegistryChange, consumeTool, retainPartialArtifacts]
  all_goals repeat' first
    | exact Or.inl rfl
    | (exact Or.inr ⟨_, by assumption⟩)
    | (unfold settleTimedOut; simp only [timeoutResultAndArtifacts])
    | split

private def RegistryNode (state : (State app)) (node : (HarnessF app) (State app)) : Prop :=
  ∀ response : Reply node.fst, RegistryChange state (node.snd response)

private theorem artifacts_step_change (s : (State app)) :
    ∀ response : Reply (step s).fst, RegistryChange s ((step s).snd response) := by
  change RegistryNode s (step s)
  cases hp : s.phase <;> simp only [step, hp]
  case stopped outcome => intro response; exact response.elim
  case controlModel =>
    intro response
    exact Or.inl (artifacts_consumeControl s none response)
  case controlTools calls =>
    intro response
    exact Or.inl (artifacts_consumeControl s (some calls) response)
  case ask call rest =>
    intro response
    cases response <;> exact Or.inl rfl
  case waiting delay =>
    intro response
    cases response <;> exact Or.inl rfl
  case model =>
    by_cases guard : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts)) = true
    · erw [if_pos guard]
      intro response
      exact Or.inl (artifacts_consumeModel s response)
    · erw [if_neg guard]; intro response; exact response.elim
  case summary =>
    cases pending : s.pendingSummary with
    | none => intro response; exact response.elim
    | some plan =>
      dsimp only
      by_cases guard : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts) && planValid s plan) = true
      · erw [if_pos guard]
        intro response
        exact Or.inl (summary_artifacts_preserved s plan response)
      · erw [if_neg guard]; intro response; exact response.elim
  case tool call rest =>
    by_cases guard : (authorized s.config s.grant call && artifactAuthorized s call && decide (0 < s.toolDispatches) && decide (s.toolDispatches ≤ s.config.maxToolCalls)) = true
    · erw [if_pos guard]
      intro response
      exact artifacts_consumeTool s call rest (response.map (app.render call.operation))
    · erw [if_neg guard]; intro response; exact response.elim

/-- Every ordinary continuation preserves registry well-formedness and retains
each previous entry as an unchanged prefix, including partial tool observations. -/
theorem artifact_registry_preserved (s : (State app)) (valid : ArtifactsValid s)
    (response : Reply (step s).fst) :
    s.artifacts <+: ((step s).snd response).artifacts ∧ ArtifactsValid ((step s).snd response) := by
  have config := config_preserved s response
  rcases artifacts_step_change s response with unchanged | ⟨offered, accepted⟩
  · exact ⟨by simp [unchanged], by simpa [ArtifactsValid, config, unchanged] using valid⟩
  · obtain ⟨extension, afterValid⟩ := registerArtifacts_contract s.config _ _ offered valid accepted
    exact ⟨extension, by simpa [ArtifactsValid, config] using afterValid⟩

theorem artifacts_init (id : String) (config : Config) (task : String) :
    ArtifactsValid (init id config task app) := by
  simp [ArtifactsValid, ArtifactRegistryValid, init, artifactBytes]

theorem reachable_artifacts_valid {id : String} {config : Config} {task : String} {state : (State app)}
    (reachable : Reachable id config task state) : ArtifactsValid state :=
  reachable.invariant (artifacts_init _ _ _)
    (fun state valid response => (artifact_registry_preserved state valid response).2)

theorem ExecutionTrace.artifacts_monotone {first last : (State app)} {events : List (ObservedStep app)}
    (trace : ExecutionTrace first events last) (valid : ArtifactsValid first) :
    first.artifacts <+: last.artifacts ∧ ArtifactsValid last :=
  trace.accumulate (r := fun before after => before.artifacts <+: after.artifacts)
    (fun _ => List.prefix_rfl) (fun left right => left.trans right)
    artifact_registry_preserved valid

/-- This is an authority check against admitted metadata, not a filesystem claim. -/
theorem emitted_application_artifact_read_registered (s : (State app)) (call : (Call app)) (id : String)
    (operation : app.artifactRead call.operation = some id) (emitted : (step s).fst = .tool call) :
    ∃ ref ∈ s.artifacts, ref.id = id := by
  cases hp : s.phase <;> simp only [step, hp] at emitted
  all_goals try contradiction
  case model =>
    by_cases guard : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts)) = true
    · simp only [guard] at emitted; contradiction
    · simp only [guard] at emitted; contradiction
  case summary =>
    cases pending : s.pendingSummary with
    | none => simp [pending] at emitted
    | some plan =>
      simp only [pending] at emitted
      by_cases guard : (decide (0 < s.modelAttempts) && decide (s.modelAttempts ≤ s.config.maxModelAttempts) && planValid s plan) = true
      · simp only [guard] at emitted; contradiction
      · simp only [guard] at emitted; contradiction
  case tool actual rest =>
    by_cases guard : (authorized s.config s.grant actual && artifactAuthorized s actual && decide (0 < s.toolDispatches) && decide (s.toolDispatches ≤ s.config.maxToolCalls)) = true
    · simp only [guard] at emitted
      cases emitted
      simp only [Bool.and_eq_true] at guard
      have admitted := guard.1.1.2
      simpa [artifactAuthorized, operation, List.any_eq_true] using admitted
    · simp only [guard] at emitted; contradiction

/-- Coding artifact reads specialize the application-level registry authority check. -/
theorem emitted_artifact_read_registered (s : State Coding.application) (call : ToolCall)
    (args : ArtifactReadArgs) (operation : call.operation = .readArtifact args)
    (emitted : (step s).fst = .tool call) : ∃ ref ∈ s.artifacts, ref.id = args.id := by
  exact emitted_application_artifact_read_registered s call args.id
    (by simp [operation, Coding.application]) emitted

/-- Recovery's explicit overlay retains the current registry when it reopens a
suspended tool position. This does not assert that recovery follows an ordinary step. -/
theorem recovery_target_retains_artifacts (cursor : (Recovery.Cursor app)) (prior : (State app))
    (accepted : Recovery.checkedTarget cursor = .ok prior) :
    prior.artifacts = cursor.state.artifacts := by
  by_cases pending : cursor.pending = true
  · by_cases invalid : (cursor.terminal || cursor.suspended.isSome) = true
    · simp [Recovery.checkedTarget, pending, invalid] at accepted
    · have eq : cursor.state = prior := by simpa [Recovery.checkedTarget, pending, invalid] using accepted
      cases eq
      rfl
  · cases saved : cursor.suspended with
    | none => simp [Recovery.checkedTarget, pending, saved] at accepted
    | some old =>
      simp only [Recovery.checkedTarget, pending, Bool.false_eq_true, ↓reduceIte, saved] at accepted
      split at accepted
      · cases action : (step old).fst <;> simp only [action] at accepted
        all_goals simp at accepted
        have fields := congrArg State.artifacts accepted
        exact fields.symm
      · simp at accepted

end Harness
