import Harness.Adapter.Native
import Harness.Adapter.JsonBounds
import Harness.Core.Journal

namespace Harness.JournalIO
open Lean

private def maxJournal : Nat := 64 * 1024 * 1024
private def maxFrame : Nat := 32 * 1024 * 1024

structure ReadResult where
  records : Array Json := #[]
  checksum : String := ""
  interrupted : Bool := false
  /-- Cursor of complete validated frames; excludes an interrupted final tail. -/
  cursor : Journal.Cursor := {}
  deriving ToJson

private def parentAndName (path : String) : IO (String × String) := do
  let p := System.FilePath.mk path
  let some name := p.fileName | throw <| IO.userError "journal path has no filename"
  return ((p.parent.getD ".").toString, name)

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
      let frame ← IO.ofExcept (JsonBounds.parse line)
      let record ← IO.ofExcept (frame.getObjVal? "record")
      let expected ← Native.sha256 (Journal.frameBase result.cursor record).compress.toUTF8
      let header ← IO.ofExcept (Journal.headerFromJson frame)
      let cursor ← IO.ofExcept <| Journal.accept result.cursor
        {header, expectedChecksum := expected, bytes := i + 1 - start}
      result := {result with records := result.records.push record, checksum := cursor.checksum, cursor}
      start := i + 1
  return {result with interrupted := start != bytes.size}

def read (path : String) : IO ReadResult := do
  let (parent, name) ← parentAndName path
  Native.withFD (Native.openDir parent) fun dir =>
    Native.withFD (Native.openReadAt dir name) fun fd => do
      unless (← Native.stat fd).kind == 1 do throw <| IO.userError "journal is not a regular file"
      decode (← readBounded fd)

/-- One sequential writer, owned by `withWriter` inside the caller's session lock.
The descriptors and validated cursor never escape as authority. Session storage
must have no concurrent external writer; stat checks detect replacement/size drift,
not malicious same-size rewrites. Calls on this handle must be serialized. -/
structure Writer where
  private mk ::
  private directory : Native.FD
  private file : Native.FD
  private name : String
  private identity : Native.FileInfo
  private head : IO.Ref (Option Journal.Cursor)

/-- Diagnostic view only. `none` means closed, in progress, or poisoned; it cannot
be converted back into a usable writer by a caller. -/
def Writer.cursor? (writer : Writer) : IO (Option Journal.Cursor) := writer.head.get

private def sameIdentity (a b : Native.FileInfo) : Bool :=
  a.kind == 1 && b.kind == 1 && a.device == b.device && a.inode == b.inode &&
    a.links == b.links

private def checkHead (writer : Writer) (cursor : Journal.Cursor) : IO Unit := do
  let opened ← Native.stat writer.file
  let named ← Native.statAt writer.directory writer.name
  unless sameIdentity opened writer.identity && sameIdentity named writer.identity &&
      opened.size == cursor.bytes && named.size == cursor.bytes do
    throw <| IO.userError "journal identity or size changed; reopen and validate before appending"

/-- A successful return acknowledges write + file sync + parent sync. No previous
frame is reread. Any failure poisons this handle, including a potentially committed
write whose sync failed; only reopening and validating can restore a cursor. -/
def Writer.append (writer : Writer) (record : Json) : IO Unit := do
  let some cursor ← writer.head.get
    | throw <| IO.userError "journal writer is closed or invalid; reopen and validate"
  writer.head.set none
  checkHead writer cursor
  let base := Journal.frameBase cursor record
  let checksum ← Native.sha256 base.compress.toUTF8
  let frame := base.mergeObj (Json.mkObj [("checksum", toJson checksum)])
  let encoded := frame.compress
  let data := (encoded ++ "\n").toUTF8
  if data.size > maxFrame then throw <| IO.userError "journal record too large"
  -- Preserve exact numeric representation, not merely numerical equality.
  match JsonBounds.parse encoded with
  | .ok decoded =>
    unless decoded == frame do
      throw <| IO.userError "journal value cannot be serialized losslessly"
  | .error _ => throw <| IO.userError "journal value cannot be serialized losslessly"
  if cursor.bytes + data.size > maxJournal then
    throw <| IO.userError "journal exceeds 64 MiB limit"
  let next ← IO.ofExcept <| Journal.accept cursor {
    header := {version := 1, sequence := cursor.sequence, previous := cursor.checksum, checksum}
    expectedChecksum := checksum, bytes := data.size}
  Native.write writer.file data
  Native.sync writer.file
  Native.sync writer.directory
  -- Detect short writes or a replaced entry before issuing a successful ack.
  checkHead writer next
  writer.head.set (some next)

/-- Validate the prefix once while holding its file lock. The caller also holds
the session lock. A torn/corrupt prefix never reaches the callback. `initial` is
available for logical replay, avoiding another read in the runner. The handle is
invalidated before its descriptors close, including when the callback throws. -/
def withWriter (path : String) (body : Writer → ReadResult → IO α) : IO α := do
  let (parent, name) ← parentAndName path
  Native.withFD (Native.openDir parent) fun directory =>
    Native.withFD (Native.openWriteAt directory name false true 384) fun file => do
      unless ← Native.flock file true false do throw <| IO.userError "journal lock failed"
      let identity ← Native.stat file
      unless identity.kind == 1 do throw <| IO.userError "journal is not a regular file"
      let initial ← Native.withFD (Native.openReadAt directory name) fun input => do
        unless sameIdentity (← Native.stat input) identity do
          throw <| IO.userError "journal changed while opening its validated prefix"
        decode (← readBounded input)
      if initial.interrupted then throw <| IO.userError "incomplete tail preserved; refusing append"
      let writer := Writer.mk directory file name identity (← IO.mkRef (some initial.cursor))
      try
        checkHead writer initial.cursor
        body writer initial
      finally writer.head.set none

/-- Safe one-shot compatibility path. Long sessions use `withWriter` once; callers
without a retained session-owned handle still revalidate on every append. -/
def append (path : String) (record : Json) : IO Unit :=
  withWriter path fun writer _ => writer.append record

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
