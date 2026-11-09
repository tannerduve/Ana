import Harness.Core.Coding
import Harness.Applications.Inventory

/-!
Independent operation-level authority contracts for the installed applications. These relations
describe dedicated-tool disclosure/mutation scope, rather than defining validity as the outcome
of the classifier. They do not prove external IO truth or confine an authorized subprocess.
Inventory aggregate rights intentionally differ from per-SKU rights.
-/
namespace Harness.ApplicationCapabilities

open Capability

/-- A list/search reads a whole requested tree; an edit observes and changes its exact file.
Process authority is the exact invocation, with its execution profile's separate trust boundary.
Artifact byte access is distinct from the automatically visible artifact catalogue metadata. -/
inductive CodingDemand : ToolOp → Access → Prop where
  | listNames (args : ListArgs) : CodingDemand (.listFiles args) (.read (.tree args.path))
  | readContents (args : ReadArgs) : CodingDemand (.readFile args) (.read (.exact args.path))
  | searchContents (args : SearchArgs) : CodingDemand (.searchFiles args) (.read (.tree args.path))
  | editPreimage (args : EditArgs) : CodingDemand (.editFile args) (.read (.exact args.path))
  | editContents (args : EditArgs) : CodingDemand (.editFile args) (.write (.exact args.path))
  | createContents (args : CreateArgs) : CodingDemand (.createFile args) (.write (.exact args.path))
  | invoke (args : ProcessArgs) : CodingDemand (.runProcess args) (.process args.argv args.cwd)
  | artifactBytes (args : ArtifactReadArgs) : CodingDemand (.readArtifact args) (.artifact args.id)

/-- The read in a reservation is intentional: the receipt contains before/remaining stock.
Warehouse queries expose counts and pagination as well as rows; no SKU-prefix inference occurs. -/
inductive InventoryDemand : Inventory.Operation → Access → Prop where
  | lookup (sku : String) :
      InventoryDemand (.lookup sku) (.resource "inventory" "lookup" (.exact sku))
  | lowStock (warehouse : String) (offset limit : Nat) :
      InventoryDemand (.lowStock warehouse offset limit)
        (.resource "inventory" "low_stock" (.exact warehouse))
  | warehouseTotals :
      InventoryDemand .warehouseTotals (.resource "inventory" "warehouse_totals" .all)
  | reservationRead (sku : String) (units : Nat) :
      InventoryDemand (.reserve sku units) (.resource "inventory" "lookup" (.exact sku))
  | reservationWrite (sku : String) (units : Nat) :
      InventoryDemand (.reserve sku units) (.resource "inventory" "reserve" (.exact sku))

theorem coding_demands_complete (needed : CodingDemand op access) :
    access ∈ Coding.application.requiredCapabilities op := by
  cases needed <;> simp [Coding.application, Coding.requiredCapabilities]

theorem coding_demands_exact (op : ToolOp) (access : Access) :
    access ∈ Coding.application.requiredCapabilities op ↔ CodingDemand op access := by
  constructor
  · intro member
    change access ∈ Coding.requiredCapabilities op at member
    cases op with
    | listFiles args =>
      have equal : access = .read (.tree args.path) := by
        simpa [Coding.requiredCapabilities] using member
      subst access
      exact .listNames args
    | readFile args =>
      have equal : access = .read (.exact args.path) := by
        simpa [Coding.requiredCapabilities] using member
      subst access
      exact .readContents args
    | searchFiles args =>
      have equal : access = .read (.tree args.path) := by
        simpa [Coding.requiredCapabilities] using member
      subst access
      exact .searchContents args
    | editFile args =>
      have alternatives : access = .read (.exact args.path) ∨ access = .write (.exact args.path) := by
        simpa [Coding.requiredCapabilities] using member
      rcases alternatives with equal | equal
      · subst access; exact .editPreimage args
      · subst access; exact .editContents args
    | createFile args =>
      have equal : access = .write (.exact args.path) := by
        simpa [Coding.requiredCapabilities] using member
      subst access
      exact .createContents args
    | runProcess args =>
      have equal : access = .process args.argv args.cwd := by
        simpa [Coding.requiredCapabilities] using member
      subst access
      exact .invoke args
    | readArtifact args =>
      have equal : access = .artifact args.id := by
        simpa [Coding.requiredCapabilities] using member
      subst access
      exact .artifactBytes args
  · exact coding_demands_complete

theorem inventory_demands_complete (needed : InventoryDemand op access) :
    access ∈ Inventory.application.requiredCapabilities op := by
  cases needed <;> simp [Inventory.application, Inventory.requiredCapabilities]

theorem inventory_demands_exact (op : Inventory.Operation) (access : Access) :
    access ∈ Inventory.application.requiredCapabilities op ↔ InventoryDemand op access := by
  constructor
  · intro member
    change access ∈ Inventory.requiredCapabilities op at member
    cases op with
    | lookup sku =>
      have equal : access = .resource "inventory" "lookup" (.exact sku) := by
        simpa [Inventory.requiredCapabilities] using member
      subst access
      exact .lookup sku
    | lowStock warehouse offset limit =>
      have equal : access = .resource "inventory" "low_stock" (.exact warehouse) := by
        simpa [Inventory.requiredCapabilities] using member
      subst access
      exact .lowStock warehouse offset limit
    | warehouseTotals =>
      have equal : access = .resource "inventory" "warehouse_totals" .all := by
        simpa [Inventory.requiredCapabilities] using member
      subst access
      exact .warehouseTotals
    | reserve sku units =>
      have alternatives : access = .resource "inventory" "lookup" (.exact sku) ∨
          access = .resource "inventory" "reserve" (.exact sku) := by
        simpa [Inventory.requiredCapabilities] using member
      rcases alternatives with equal | equal
      · subst access; exact .reservationRead sku units
      · subst access; exact .reservationWrite sku units
  · exact inventory_demands_complete

theorem coding_demands_nonempty (op : ToolOp) :
    Coding.application.requiredCapabilities op ≠ [] := by
  cases op <;> simp [Coding.application, Coding.requiredCapabilities]

theorem inventory_demands_nonempty (op : Inventory.Operation) :
    Inventory.application.requiredCapabilities op ≠ [] := by
  cases op <;> simp [Inventory.application, Inventory.requiredCapabilities]

/-- Necessary hypothesis for applying generic capability attenuation to the full app policy:
changing this ceiling cannot make the application's independent decision more permissive. -/
theorem coding_policy_independent (config : Config) (permissions : Capability.Policy) (op : ToolOp) :
    Coding.application.policy {config with capabilityPolicy := permissions} op =
      Coding.application.policy config op := by
  cases op <;> rfl

theorem inventory_policy_independent (config : Config) (permissions : Capability.Policy)
    (op : Inventory.Operation) :
    Inventory.application.policy {config with capabilityPolicy := permissions} op =
      Inventory.application.policy config op := by
  rfl

end Harness.ApplicationCapabilities
