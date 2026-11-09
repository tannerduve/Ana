import Harness.Adapter.JsonBounds
import Lean.Data.Json.Printer

namespace Tests.JsonBounds
open Harness Lean

private def ensure (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw <| IO.userError ("JSON bounds: " ++ label)

private def rejected (value : Except String α) : Bool := !value.isOk

private def repeated (value : String) (count : Nat) : String :=
  String.join (List.replicate count value)

private def arrayOf (value : String) (count : Nat) : String :=
  "[" ++ String.intercalate "," (List.replicate count value) ++ "]"

def run : IO Unit := do
  for value in ["0", "-23", "2.5", "1e20", "1e-20", "1e4096", "1e-4096", "1e+0004096"] do
    ensure (Harness.JsonBounds.parse value).isOk ("ordinary admitted number " ++ value)
  for value in ["1e4097", "1e-4097", "0e1000000000", "1e+1000000000"] do
    ensure (rejected (Harness.JsonBounds.parse value)) ("exponent refusal " ++ value)
  ensure (Harness.JsonBounds.parse (repeated "1" 4096)).isOk "4096 literal digits"
  ensure (rejected (Harness.JsonBounds.parse (repeated "1" 4097))) "4097 literal digits refused"
  ensure (Harness.JsonBounds.parse (repeated "[" 128 ++ "0" ++ repeated "]" 128)).isOk "128 containers"
  ensure (rejected (Harness.JsonBounds.parse (repeated "[" 129 ++ "0" ++ repeated "]" 129))) "129 containers refused"
  let quoted := (Json.str ("1e1000000000 " ++ repeated "[" 129 ++ " \\\" braces { } 🦀")).compress
  ensure (Harness.JsonBounds.parse quoted).isOk "numbers and containers in escaped quoted text"
  ensure (rejected (Harness.JsonBounds.parse ("[" ++ quoted ++ ",1e1000000000]"))) "quote closes before numeric refusal"
  ensure (Harness.JsonBounds.check (arrayOf "1e4096" 255)).isOk "aggregate just below numeric work cap"
  ensure (rejected (Harness.JsonBounds.check (arrayOf "1e4096" 256))) "aggregate above numeric work cap"
  let spent ← IO.ofExcept (Harness.JsonBounds.checkWork (arrayOf "1e4096" 128))
  ensure (rejected (Harness.JsonBounds.checkWork (arrayOf "1e4096" 128) spent)) "shared budget across parses"
  ensure (Harness.JsonBounds.check "[1e+,]").isOk "scanner does not replace grammar"
  ensure (rejected (Harness.JsonBounds.parse "[1e+,]")) "original grammar still rejects invalid input"
  IO.println "JSON lexical resource bounds passed"

end Tests.JsonBounds
