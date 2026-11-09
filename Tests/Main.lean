import Tests.ProofBoundaries
import Tests.JsonBounds
import Tests.Core
import Tests.SSE
import Tests.Provider
import Tests.Recovery
import Tests.RecoveryTransitions
import Tests.Properties
import Tests.Compaction
import Tests.ContentParser
import Tests.ResponseRepair
import Tests.BudgetContext
import Tests.SettledTimeout
import Tests.Inventory
import Tests.InventoryReservations
import Tests.ApplicationPolicy
import Tests.Applications
import Tests.Turns
import Tests.ApplicationLaws
import Tests.Capabilities
import Tests.ApplicationCapabilities

def main : IO Unit := do
  Tests.JsonBounds.run
  Tests.Core.run
  Tests.SSE.run
  Tests.Provider.run
  Tests.Recovery.run
  Tests.RecoveryTransitions.run
  Tests.Properties.run
  Tests.Compaction.run
  Tests.ContentParser.run
  Tests.ResponseRepair.run
  Tests.BudgetContext.run
  Tests.SettledTimeout.run
  Tests.Inventory.run
  Tests.InventoryReservations.run
  Tests.ApplicationPolicy.run
  Tests.Turns.run
  Tests.ApplicationLaws.run
  Tests.Capabilities.run
  Tests.ApplicationCapabilities.run
  IO.println "All executable Lean checks passed."
