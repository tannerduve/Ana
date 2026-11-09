import Harness.Proofs.CapabilityAlgebra
import Harness.Proofs.Administrative
import Harness.Proofs.ApplicationCapabilities

/-!
Connect capability containment to the actual authorization and dispatch functions.
An exact approval never overrides a resource ceiling. The replay result includes
recovery and follow-up records through the existing frozen-configuration invariant.
These statements concern application-declared authority; physical effects remain
the responsibility of the corresponding tool adapters and execution profile.
-/
namespace Harness

variable {app : Application}

theorem authorized_capability_contract (config : Config) (grant : Option (Call app))
    (call : Call app) :
    authorized config grant call = true ↔
      capabilitiesPermit config call = true ∧
        (approvalPolicy config call = .allow ∨
          approvalPolicy config call = .ask ∧ grant = some call) := by
  cases permitted : capabilitiesPermit config call <;>
    simp [authorized, policy, permitted]

/-- Even a matching grant cannot turn a resource denial into authority. -/
theorem denied_capability_not_authorized (config : Config) (grant : Option (Call app))
    (call : Call app) (denied : capabilitiesPermit config call = false) :
    authorized config grant call = false := by
  simp [authorized, policy, denied]

/-- This holds for any state, including an invalid or forged serialized tool phase. -/
theorem emitted_tool_capabilities (state : State app) (call : Call app)
    (emitted : (step state).1 = .tool call) :
    Capability.permitsAll state.config.capabilityPolicy
      (app.requiredCapabilities call.operation) = true :=
  ((authorized_capability_contract state.config state.grant call).mp
    (emitted_tool_authorized state call emitted)).1

theorem emitted_tool_requires_capabilities (state : State app) (call : Call app)
    (emitted : (step state).1 = .tool call) :
    app.requiredCapabilities call.operation ≠ [] ∧
      ∀ access ∈ app.requiredCapabilities call.operation,
        Capability.permits state.config.capabilityPolicy access = true := by
  have allowed := emitted_tool_capabilities state call emitted
  exact ⟨Capability.permitsAll_nonempty allowed,
    fun _ member => Capability.permitsAll_member allowed member⟩

/-- The independent application requirement, not merely the classifier list,
is authorized whenever the corresponding coding operation is emitted. -/
theorem coding_emitted_required_access (state : State) (call : ToolCall)
    (emitted : (step state).1 = .tool call)
    (needed : ApplicationCapabilities.CodingDemand call.operation access) :
    Capability.permits state.config.capabilityPolicy access = true :=
  Capability.permitsAll_member (emitted_tool_capabilities state call emitted)
    (ApplicationCapabilities.coding_demands_complete needed)

theorem inventory_emitted_required_access (state : State Inventory.application)
    (call : Call Inventory.application) (emitted : (step state).1 = .tool call)
    (needed : ApplicationCapabilities.InventoryDemand call.operation access) :
    Capability.permits state.config.capabilityPolicy access = true :=
  Capability.permitsAll_member (emitted_tool_capabilities state call emitted)
    (ApplicationCapabilities.inventory_demands_complete needed)

theorem reachable_tool_capabilities {id task : String} {config : Config} {state : State app}
    (reachable : Reachable id config task state) (call : Call app)
    (emitted : (step state).1 = .tool call) :
    Capability.permitsAll config.capabilityPolicy
      (app.requiredCapabilities call.operation) = true := by
  have allowed := emitted_tool_capabilities state call emitted
  rw [(reachable_core_valid reachable).frozen] at allowed
  exact allowed

/-- Accepted replay includes administrative recovery, resolution and new turns. -/
theorem replay_tool_capabilities (id : String) (config : Config) (task : String)
    (records : List Lean.Json) (cursor : Recovery.Cursor app)
    (accepted : Recovery.replay (init id config task app) records = .ok cursor)
    (call : Call app) (emitted : (step cursor.state).1 = .tool call) :
    Capability.permitsAll config.capabilityPolicy
      (app.requiredCapabilities call.operation) = true := by
  have allowed := emitted_tool_capabilities cursor.state call emitted
  rw [(Recovery.replay_core_valid id config task records cursor accepted).current.frozen] at allowed
  exact allowed

/-- Containment only changes the capability field. An arbitrary application policy
may inspect that field, so its independence is an explicit, necessary hypothesis. -/
theorem authorization_under_contained_policy (config : Config) (permissions : Capability.Policy)
    (contained : Capability.Contained permissions config.capabilityPolicy)
    (grant : Option (Call app)) (call : Call app)
    (independent : app.policy {config with capabilityPolicy := permissions} call.operation =
      app.policy config call.operation)
    (authorizedChild : authorized {config with capabilityPolicy := permissions} grant call = true) :
    authorized config grant call = true := by
  obtain ⟨scope, approval⟩ :=
    (authorized_capability_contract {config with capabilityPolicy := permissions} grant call).mp authorizedChild
  apply (authorized_capability_contract config grant call).mpr
  constructor
  · exact Capability.permitsAll_of_contained contained scope
  · simpa [approvalPolicy, independent] using approval

/-- Accepting the executable checker suffices for authorization containment. -/
theorem authorization_under_checked_policy (config : Config) (permissions : Capability.Policy)
    (checked : Capability.checkContained permissions config.capabilityPolicy = true)
    (grant : Option (Call app)) (call : Call app)
    (independent : app.policy {config with capabilityPolicy := permissions} call.operation =
      app.policy config call.operation)
    (authorizedChild : authorized {config with capabilityPolicy := permissions} grant call = true) :
    authorized config grant call = true :=
  authorization_under_contained_policy config permissions (Capability.checkContained_sound checked)
    grant call independent authorizedChild

theorem coding_authorization_restricts (config : Config) (layer : List Capability.Access)
    (grant : Option ToolCall) (call : ToolCall)
    (authorizedChild : authorized
      {config with capabilityPolicy := Capability.restrict config.capabilityPolicy layer} grant call = true) :
    authorized config grant call = true :=
  authorization_under_contained_policy config _ (Capability.restrict_contained_parent _ _)
    grant call (ApplicationCapabilities.coding_policy_independent config _ call.operation) authorizedChild

theorem inventory_authorization_restricts (config : Config) (layer : List Capability.Access)
    (grant : Option (Call Inventory.application)) (call : Call Inventory.application)
    (authorizedChild : authorized
      {config with capabilityPolicy := Capability.restrict config.capabilityPolicy layer} grant call = true) :
    authorized config grant call = true :=
  authorization_under_contained_policy config _ (Capability.restrict_contained_parent _ _)
    grant call (ApplicationCapabilities.inventory_policy_independent config _ call.operation) authorizedChild

end Harness
