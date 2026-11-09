import Lean.Data.Json.Parser

/-!
Resource admission for JSON read from providers and journals. This linear scan
only limits nesting and numeric work; Lean's existing parser remains responsible
for grammar and values. Quoted strings, including escaped quotes, are untouched.
The work bound is a conservative decimal-digit budget, not a memory theorem.
-/
namespace Harness.JsonBounds

private def maximumDigits : Nat := 4096
private def maximumExponent : Nat := 4096
private def maximumDepth : Nat := 128
private def maximumWork : Nat := 1024 * 1024

private structure Scan where
  quoted : Bool := false
  escaped : Bool := false
  depth : Nat := 0
  number : Bool := false
  digits : Nat := 0
  exponent : Bool := false
  negativeExponent : Bool := false
  magnitude : Nat := 0
  work : Nat := 0

private def digit (byte : UInt8) : Bool := byte >= 48 && byte <= 57

private def numeric (byte : UInt8) : Bool :=
  digit byte || byte == 45 || byte == 43 || byte == 46 || byte == 69 || byte == 101

private def numberByte (state : Scan) (byte : UInt8) : Except String Scan := do
  if digit byte then
    let digits := state.digits + 1
    if digits > maximumDigits then throw "JSON numeric literal exceeds 4096 digits"
    let magnitude := if state.exponent then state.magnitude * 10 + (byte.toNat - 48) else 0
    if magnitude > maximumExponent then throw "JSON exponent exceeds magnitude 4096"
    let extra := if state.exponent && !state.negativeExponent then magnitude - state.magnitude else 0
    let work := state.work + 1 + extra
    if work > maximumWork then throw "JSON cumulative numeric work exceeds 1048576 digits"
    return {state with digits, magnitude, work}
  else if byte == 69 || byte == 101 then
    return {state with exponent := true}
  else if byte == 45 && state.exponent then
    return {state with negativeExponent := true}
  else return state

private def next (state : Scan) (byte : UInt8) : Except String Scan := do
  if state.quoted then
    if state.escaped then return {state with escaped := false}
    else if byte == 92 then return {state with escaped := true}
    else if byte == 34 then return {state with quoted := false}
    else return state
  else if state.number && numeric byte then numberByte state byte
  else
    let state := {state with number := false, digits := 0, exponent := false, negativeExponent := false, magnitude := 0}
    if byte == 34 then return {state with quoted := true}
    else if byte == 91 || byte == 123 then
      if state.depth >= maximumDepth then throw "JSON nesting exceeds 128 containers"
      return {state with depth := state.depth + 1}
    else if byte == 93 || byte == 125 then return {state with depth := state.depth - 1}
    else if digit byte || byte == 45 then numberByte {state with number := true} byte
    else return state

/-- Total, linear lexical admission. It deliberately does not accept/reject JSON
syntax; accepted input still passes through the pinned Lean parser. Existing
callers additionally bound the number of input bytes. -/
def checkWork (input : String) (spent : Nat := 0) : Except String Nat := do
  if spent > maximumWork then throw "JSON cumulative numeric work exceeds 1048576 digits"
  let mut state : Scan := {work := spent}
  for byte in input.toUTF8 do
    state ← next state byte
  return state.work

/-- Check one bounded input independently. -/
def check (input : String) : Except String Unit := do
  let _ ← checkWork input
  return ()

/-- Parse without permitting a short exponent to trigger unbounded expansion. -/
def parseWithWork (input : String) (spent : Nat := 0) : Except String (Lean.Json × Nat) := do
  let work ← checkWork input spent
  let value ← Lean.Json.parse input
  return (value, work)

/-- An independent input receives the fixed 1 MiB numeric-work allowance. -/
def parse (input : String) : Except String Lean.Json :=
  (parseWithWork input).map Prod.fst

end Harness.JsonBounds
