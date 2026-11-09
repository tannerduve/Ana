import Tests.Core
import Tests.Provider
import Tests.Recovery
import Tests.Properties

def main : IO Unit := do
  Tests.Core.run
  Tests.Provider.run
  Tests.Recovery.run
  Tests.Properties.run
  IO.println "All executable Lean checks passed."
