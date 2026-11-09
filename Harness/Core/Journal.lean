import Lean

/-! Pure framing and append-cursor bookkeeping, shared by journal validation and IO.
Checksums are supplied by the native hashing adapter. These definitions do not
claim that bytes reached durable storage; the IO writer advances only after sync. -/
namespace Harness.Journal
open Lean

structure Cursor where
  sequence : Nat := 0
  checksum : String := ""
  bytes : Nat := 0
  deriving Repr, BEq, DecidableEq, ToJson

structure Header where
  version : Nat
  sequence : Nat
  previous : String
  checksum : String
  deriving Repr, BEq, DecidableEq

def frameBase (cursor : Cursor) (record : Json) : Json :=
  Json.mkObj [("v", toJson (1 : Nat)), ("seq", toJson cursor.sequence),
    ("previous", toJson cursor.checksum), ("record", record)]

def headerFromJson (frame : Json) : Except String Header := do
  return {
    version := ← frame.getObjValAs? Nat "v"
    sequence := ← frame.getObjValAs? Nat "seq"
    previous := ← frame.getObjValAs? String "previous"
    checksum := ← frame.getObjValAs? String "checksum"}

/-- `bytes` includes this frame's LF delimiter, never a partial following frame. -/
structure CheckedFrame where
  header : Header
  expectedChecksum : String
  bytes : Nat
  deriving Repr

def advance (cursor : Cursor) (checksum : String) (bytes : Nat) : Cursor :=
  {sequence := cursor.sequence + 1, checksum, bytes := cursor.bytes + bytes}

/-- Accept exactly the next link; neither a sequence gap nor a foreign predecessor
can update the cursor. The hash adapter supplies the digest of `frameBase`. -/
def accept (cursor : Cursor) (frame : CheckedFrame) : Except String Cursor :=
  if frame.header.version == 1 && frame.header.sequence == cursor.sequence &&
      frame.header.previous == cursor.checksum &&
      frame.header.checksum == frame.expectedChecksum && frame.bytes > 0 then
    .ok (advance cursor frame.header.checksum frame.bytes)
  else .error s!"invalid journal frame {cursor.sequence}; automatic replay refused"

def validatePrefix (cursor : Cursor) (frames : List CheckedFrame) : Except String Cursor :=
  frames.foldlM accept cursor

end Harness.Journal
