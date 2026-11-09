import Harness.Adapter.Native

namespace Harness.JournalIO
open Lean

private def maxJournal : Nat := 64 * 1024 * 1024
private def maxFrame : Nat := 32 * 1024 * 1024

structure ReadResult where
  records : Array Json := #[]
  checksum : String := ""
  interrupted : Bool := false
  deriving ToJson

private def parentAndName (path : String) : IO (String × String) := do
  let p := System.FilePath.mk path
  let some name := p.fileName | throw <| IO.userError "journal path has no filename"
  return ((p.parent.getD ".").toString, name)

private def frameBase (seq : Nat) (previous : String) (record : Json) : Json :=
  Json.mkObj [("v", toJson (1 : Nat)), ("seq", toJson seq),
    ("previous", toJson previous), ("record", record)]

private def readBounded (fd : Native.FD) : IO ByteArray := do
  if (← Native.stat fd).size > maxJournal then
    throw <| IO.userError "journal exceeds 64 MiB limit"
  let mut data := ByteArray.empty
  for _ in [:maxJournal / 65536 + 2] do
    let chunk ← Native.read fd 65536
    if chunk.isEmpty then return data
    data := data ++ chunk
    if data.size > maxJournal then throw <| IO.userError "journal exceeds 64 MiB limit"
  throw <| IO.userError "journal read limit exceeded"

/-- Validate every complete frame. A torn final frame remains evidence, never an observation. -/
private def decode (bytes : ByteArray) : IO ReadResult := do
  let mut result : ReadResult := {}
  let mut start := 0
  for i in [:bytes.size] do
    if i - start > maxFrame then throw <| IO.userError "oversized journal frame"
    if bytes[i]! == 10 then
      let some line := String.fromUTF8? (bytes.extract start i)
        | throw <| IO.userError "invalid UTF-8 in journal frame"
      let frame ← IO.ofExcept (Json.parse line)
      let record ← IO.ofExcept (frame.getObjVal? "record")
      let expected ← Native.sha256 (frameBase result.records.size result.checksum record).compress.toUTF8
      unless (frame.getObjValAs? Nat "v").toOption == some 1 &&
          (frame.getObjValAs? Nat "seq").toOption == some result.records.size &&
          (frame.getObjValAs? String "previous").toOption == some result.checksum &&
          (frame.getObjValAs? String "checksum").toOption == some expected do
        throw <| IO.userError s!"invalid journal frame {result.records.size}; automatic replay refused"
      result := {result with records := result.records.push record, checksum := expected}
      start := i + 1
  return {result with interrupted := start != bytes.size}

def read (path : String) : IO ReadResult := do
  let (parent, name) ← parentAndName path
  Native.withFD (Native.openDir parent) fun dir =>
    Native.withFD (Native.openReadAt dir name) fun fd => do
      unless (← Native.stat fd).kind == 1 do throw <| IO.userError "journal is not a regular file"
      decode (← readBounded fd)

/-- The caller holds the session lock; this additional lock protects a single append. -/
def append (path : String) (record : Json) : IO Unit := do
  let (parent, name) ← parentAndName path
  Native.withFD (Native.openDir parent) fun dir =>
    Native.withFD (Native.openWriteAt dir name false true 384) fun fd => do
      unless ← Native.flock fd true false do throw <| IO.userError "journal lock failed"
      unless (← Native.stat fd).kind == 1 do throw <| IO.userError "journal is not a regular file"
      let history ← Native.withFD (Native.openReadAt dir name) fun input => do
        decode (← readBounded input)
      if history.interrupted then throw <| IO.userError "incomplete tail preserved; refusing append"
      let base := frameBase history.records.size history.checksum record
      let checksum ← Native.sha256 base.compress.toUTF8
      let data := ((base.mergeObj (Json.mkObj [("checksum", toJson checksum)])).compress ++ "\n").toUTF8
      if data.size > maxFrame then throw <| IO.userError "journal record too large"
      if (← Native.stat fd).size + data.size > maxJournal then
        throw <| IO.userError "journal exceeds 64 MiB limit"
      Native.write fd data
      Native.sync fd
      Native.sync dir

private def ensureParents (path : System.FilePath) : Nat → IO Unit
  | 0 => throw <| IO.userError "session directory nesting limit exceeded"
  | fuel + 1 => do
    if ← path.pathExists then
      Native.withFD (Native.openDir path.toString) (fun _ => pure ())
    else
      let parent := path.parent.getD "."
      ensureParents parent fuel
      try Native.mkdir path.toString 448
      catch e =>
        unless ← path.pathExists do throw e
      Native.withFD (Native.openDir path.toString) (fun fd => Native.sync fd)
      Native.withFD (Native.openDir parent.toString) (fun fd => Native.sync fd)

/-- Exclusive leaf creation; parent links are flushed before initial session state. -/
def createSession (path : String) : IO Unit := do
  let target := System.FilePath.mk path
  let parent := target.parent.getD "."
  ensureParents parent 256
  Native.mkdir path 448
  Native.withFD (Native.openDir path) (fun fd => Native.sync fd)
  Native.withFD (Native.openDir parent.toString) (fun fd => Native.sync fd)

end Harness.JournalIO
