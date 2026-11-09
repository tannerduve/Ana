import Harness.Core.Artifacts
import Harness.Adapter.RuntimeTypes
import Harness.Adapter.Native

/-! Session-local immutable output storage. Blob contents and metadata are flushed
before references can enter the journal. Retrieval accepts only core-admitted IDs.
The session lock and trusted directory exclude concurrent writers. -/
namespace Harness.ArtifactIO
open Lean Native

private def readChunks (fd : FD) (maximum : Nat) : Nat → ByteArray → IO ByteArray
  | 0, _ => throw <| IO.userError "artifact read exceeded collection bound"
  | fuel + 1, bytes => do
    let chunk ← Native.read fd (min 65536 (maximum + 1 - bytes.size)).toUInt64
    if chunk.isEmpty then return bytes
    let bytes := bytes ++ chunk
    if bytes.size > maximum then throw <| IO.userError "artifact exceeds supported size"
    readChunks fd maximum fuel bytes

private def readBounded (fd : FD) (maximum : Nat) : IO ByteArray := do
  let info ← Native.stat fd
  unless info.kind == 1 && info.links == 1 do
    throw <| IO.userError "artifact must be an unaliased regular file"
  readChunks fd maximum (maximum / 65536 + 3) ByteArray.empty

private def validateLimits (ctx : ToolContext) : IO Unit := do
  if ctx.maxArtifactBytes > 16 * 1024 * 1024 || ctx.maxSessionArtifactBytes > 256 * 1024 * 1024 then
    throw <| IO.userError "artifact limits exceed supported bounds (16 MiB each, 256 MiB per session)"

private def usedBytes (directory : FD) : IO Nat := do
  let names ← Native.listDir directory 4096
  let mut total := 0
  for name in names do
    let info ← Native.statAt directory name
    unless info.kind == 1 do throw <| IO.userError "unexpected non-file in artifact storage"
    -- Include incomplete temporary blobs left by a crash. Metadata has its own
    -- fixed record/count bounds; it does not consume the output-byte allowance.
    unless name.endsWith ".json" do total := total + info.size
  return total

def availableBytes (ctx : ToolContext) : IO Nat := do
  validateLimits ctx
  IO.FS.createDirAll ctx.artifactDir
  withFD (openDir ctx.artifactDir) fun directory => do
    return ctx.maxSessionArtifactBytes - (← usedBytes directory)

private def publish (directory : FD) (name : String) (bytes : ByteArray) : IO Unit := do
  let (temporary, fd) ← Native.mkTempAt directory 384
  try
    try
      Native.write fd bytes
      Native.sync fd
    finally Native.close fd
    -- No replacement of an existing artifact identity, even on a collision.
    Native.linkAt directory temporary name
    Native.unlinkAt directory temporary
    Native.sync directory
  finally
    try Native.unlinkAt directory temporary catch _ => pure ()

def store (ctx : ToolContext) (label : String) (bytes : ByteArray)
    (totalBytes : Nat) : IO ArtifactRef := do
  validateLimits ctx
  unless ["output", "stdout", "stderr"].contains label do
    throw <| IO.userError "unsupported artifact label"
  if bytes.size > totalBytes then throw <| IO.userError "artifact length exceeds observed output"
  IO.FS.createDirAll ctx.artifactDir
  -- Persist creation of the artifact directory before any completion references it.
  withFD (openDir ((System.FilePath.mk ctx.artifactDir).parent.getD ".").toString) Native.sync
  withFD (openDir ctx.artifactDir) fun directory => do
    -- Two published files and at most one additional temporary/link entry.
    -- Metadata is outside the output-byte quota, but each record and the total
    -- directory entry count have independent fixed bounds.
    let entries ← Native.listDir directory 4096
    if entries.size + 3 > 4096 then
      throw <| IO.userError "artifact metadata entry allowance exhausted"
    let remaining := ctx.maxSessionArtifactBytes - (← usedBytes directory)
    let retained := bytes.extract 0 (min remaining ctx.maxArtifactBytes)
    let (nonce, fd) ← Native.mkTempAt directory 384
    Native.close fd
    let id := "a-" ++ (← Native.sha256 nonce.toUTF8)
    Native.unlinkAt directory nonce
    let ref : ArtifactRef := {
      id, label, sha256 := ← Native.sha256 retained, storedBytes := retained.size,
      totalBytes, truncated := retained.size < totalBytes }
    let metadata := (toJson ref).compress.toUTF8
    if metadata.size > 4096 then throw <| IO.userError "artifact metadata exceeds its record bound"
    publish directory (id ++ ".blob") retained
    publish directory (id ++ ".json") metadata
    return ref

private def hexadecimal (bytes : ByteArray) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut result := ""
  for byte in bytes do
    result := result.push digits[byte.toNat / 16]!
    result := result.push digits[byte.toNat % 16]!
  return result

/-- Byte offsets are exact. Binary data or ranges cutting a UTF-8 sequence use
hexadecimal encoding; nextOffset always names the first unread byte. -/
def read (ctx : ToolContext) (args : ArtifactReadArgs) : IO ToolResult := do
  validateLimits ctx
  let some expected := ctx.artifacts.find? (fun ref => ref.id == args.id)
    | throw <| IO.userError "unknown artifact ID in this session"
  unless expected.id.startsWith "a-" && artifactHex (expected.id.drop 2 |>.toString) do
    throw <| IO.userError "invalid artifact identity"
  if args.length == 0 || args.length > 65536 || ctx.outputBytes < 512 then
    throw <| IO.userError "artifact reads require length 1..65536 and an output allowance of at least 512 bytes"
  withFD (openDir ctx.artifactDir) fun directory => do
    let metadata ← withFD (openReadAt directory (args.id ++ ".json")) fun fd => readBounded fd 4096
    let actual : ArtifactRef ← IO.ofExcept <| do
      let some text := String.fromUTF8? metadata | throw "artifact metadata is not UTF-8"
      fromJson? (← Json.parse text)
    unless actual == expected do throw <| IO.userError "artifact metadata differs from the admitted identity"
    let bytes ← withFD (openReadAt directory (args.id ++ ".blob")) fun fd => readBounded fd ctx.maxArtifactBytes
    unless bytes.size == expected.storedBytes && (← Native.sha256 bytes) == expected.sha256 do
      throw <| IO.userError "artifact contents failed length/hash validation"
    if args.offset > bytes.size then throw <| IO.userError "artifact offset exceeds retained bytes"
    let count := min args.length ((min ctx.outputBytes 1048576 - 256) / 6)
    let part := bytes.extract args.offset (args.offset + count)
    let (encoding, content) := match String.fromUTF8? part with
      | some text => ("utf-8", text)
      | none => ("hex", hexadecimal part)
    return {text := (Json.mkObj [
      ("id", toJson args.id), ("offset", toJson args.offset),
      ("nextOffset", toJson (args.offset + part.size)),
      ("endOfRetainedContent", toJson (args.offset + part.size == bytes.size)),
      ("truncated", toJson expected.truncated), ("encoding", toJson encoding),
      ("content", toJson content)]).compress}

end Harness.ArtifactIO
