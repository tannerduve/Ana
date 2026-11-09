import Harness.Adapter.Native
import Harness.Adapter.RuntimeTypes
import Harness.Adapter.ArtifactIO

namespace Harness.FilesystemIO
open Lean
open Native

private def maxFileBytes : Nat := 8 * 1024 * 1024
private def maxArtifactBytes : Nat := 16 * 1024 * 1024

private def components (path : String) : IO (List String) := do
  let parts := path.splitOn "/"
  if path.isEmpty || path.startsWith "/" || path.contains '\x00' ||
      parts.contains ".." || parts.contains "" || parts.length > 64 then
    throw <| IO.userError "path must be workspace-relative, without parent traversal or symlinks (maximum depth 64)"
  return parts.filter (· != ".")

private def withParts (fd : FD) (parts : List String) (body : FD → IO α) : IO α :=
  match parts with
  | [] => body fd
  | part :: rest => withFD (openDirAt fd part) fun child => withParts child rest body

/-- The callback owns no descriptor. All directory descriptors remain live until it returns. -/
def withWorkspaceDir (workspace path : String) (body : FD → IO α) : IO α := do
  let parts ← components path
  withFD (openDir workspace) fun root => withParts root parts body

private def withParent (workspace path : String) (body : FD → String → IO α) : IO α := do
  let parts ← components path
  match parts.reverse with
  | [] => throw <| IO.userError "a file path cannot be the workspace root"
  | name :: ancestors =>
    withFD (openDir workspace) fun root => withParts root ancestors.reverse fun parent => body parent name

private def readChunks (fd : FD) (maximum : Nat) : Nat → ByteArray → IO ByteArray
  | 0, _ => throw <| IO.userError "file read exceeded collection bound"
  | fuel + 1, bytes => do
    let chunk ← Native.read fd (UInt64.ofNat (min 65536 (maximum + 1 - bytes.size)))
    if chunk.isEmpty then return bytes
    let bytes := bytes ++ chunk
    if bytes.size > maximum then throw <| IO.userError s!"file exceeds {maximum}-byte adapter limit"
    readChunks fd maximum fuel bytes

def readBounded (fd : FD) (maximum : Nat) : IO ByteArray :=
  readChunks fd maximum (maximum / 65536 + 3) ByteArray.empty

private def readAt (parent : FD) (name : String) : IO ByteArray :=
  withFD (openReadAt parent name) fun fd => do
    unless (← Native.stat fd).kind == 1 do throw <| IO.userError "only regular files can be read"
    readBounded fd maxFileBytes

private def readFile (workspace path : String) : IO ByteArray :=
  withParent workspace path readAt

private def utf8 (bytes : ByteArray) : IO String :=
  match String.fromUTF8? bytes with
  | some text => pure text
  | none => throw <| IO.userError "file is not valid UTF-8"

/-- Bounded, no-follow identity observation for recovery; never changes a file. -/
def fileIdentity (workspace path : String) : IO String := do
  Native.sha256 (← readFile workspace path)

/-- Before recording recovery, settle the matched file and its directory entry.
The original process may have died between rename and directory synchronization.
The same single-writer assumption as atomicWrite applies. -/
def confirmFileIdentity (workspace path expected : String) : IO String :=
  withParent workspace path fun parent name =>
    withFD (openReadAt parent name) fun fd => do
      unless (← Native.stat fd).kind == 1 do throw <| IO.userError "recovery target is not a regular file"
      let actual ← Native.sha256 (← readBounded fd maxFileBytes)
      unless actual == expected do throw <| IO.userError "recovery target changed before synchronization"
      Native.sync fd
      Native.sync parent
      return actual

/-- Compute the intended edit identity before its durable dispatch intent.
Execution still rechecks the preimage; concurrent writers remain unsupported. -/
def editIdentities (workspace : String) (args : EditArgs) : IO (String × String) := do
  let bytes ← readFile workspace args.path
  let preimage ← Native.sha256 bytes
  unless preimage == args.expectedSha256 do
    throw <| IO.userError "preimage changed; read the file again before editing"
  let text ← utf8 bytes
  if args.old.isEmpty || (text.splitOn args.old).length != 2 then
    throw <| IO.userError "old must match exactly once; choose a larger unique span"
  let postimage := (text.replace args.old args.new).toUTF8
  if postimage.size > maxFileBytes then throw <| IO.userError "new content exceeds file-size limit"
  return (preimage, ← Native.sha256 postimage)

/-- Output text originates in valid UTF-8. A byte cap may split at most one codepoint. -/
def utf8Prefix (bytes : ByteArray) (maximum : Nat) : String := Id.run do
  let retained := bytes.extract 0 maximum
  for removed in [0:4] do
    if let some text := String.fromUTF8? (retained.extract 0 (retained.size - removed)) then return text
  return ""

private def boundedResult (ctx : ToolContext) (text : String) (sha : Option String := none)
    (actualBytes : Option Nat := none) : IO ToolResult := do
  let bytes := text.toUTF8
  let total := actualBytes.getD bytes.size
  let limit := min ctx.outputBytes (1024 * 1024)
  if total ≤ limit then return {text, sha256 := sha}
  let ref ← ArtifactIO.store ctx "output" bytes (max total bytes.size)
  let suffix := if ref.truncated then
    s!"\n[artifact contains only first {ref.storedBytes} bytes]" else ""
  let output := utf8Prefix bytes limit ++ s!"\n[output truncated: {total} bytes produced; use artifact ID {ref.id}]" ++ suffix
  return {text := output, sha256 := sha, artifacts := #[ref]}

private def cancelled (ctx : ToolContext) : IO Bool := do
  if ← Native.isCancelled then return true
  return ← (System.FilePath.mk ctx.cancelPath).pathExists

private def ensureActive (ctx : ToolContext) (deadline : Nat) : IO Unit := do
  if ← cancelled ctx then throw <| IO.userError "operation cancelled"
  if (← IO.monoMsNow) ≥ deadline then throw <| IO.userError "operation deadline exceeded"

private def ignored (name : String) : Bool :=
  [".git", ".lake", "node_modules", "__pycache__"].contains name

private def walk (ctx : ToolContext) (deadline : Nat) (visited : IO.Ref Nat)
    (fd : FD) (pathPrefix : String) : Nat → IO (Array String)
  | 0 => throw <| IO.userError "directory depth exceeds 64"
  | depth + 1 => do
    let remaining := 10000 - (← visited.get)
    let names ← Native.listDir fd (UInt32.ofNat remaining)
    visited.modify (· + names.size)
    let mut files := #[]
    for name in names.qsort (· < ·) do
      ensureActive ctx deadline
      unless ignored name do
        let path := if pathPrefix.isEmpty then name else pathPrefix ++ "/" ++ name
        let info ← statAt fd name
        if info.kind == 1 then files := files.push path
        else if info.kind == 2 then
          let nested ← withFD (openDirAt fd name) fun child => walk ctx deadline visited child path depth
          files := files ++ nested
    return files

private def filesUnder (ctx : ToolContext) (deadline : Nat) (path : String) : IO (Array String) := do
  let parts ← components path
  let visited ← IO.mkRef 0
  withWorkspaceDir ctx.workspace path fun fd =>
    walk ctx deadline visited fd (String.intercalate "/" parts) 65

private def searchPaths (ctx : ToolContext) (deadline : Nat) (path : String) : IO (Array String) := do
  let parts ← components path
  if !parts.isEmpty then
    let info ← withParent ctx.workspace path statAt
    if info.kind == 1 then return #[String.intercalate "/" parts]
    unless info.kind == 2 do throw <| IO.userError "search path must be a regular file or directory"
  filesUnder ctx deadline path

private def lines (text : String) : List String :=
  if text.isEmpty then []
  else if text.endsWith "\n" then (text.splitOn "\n").dropLast else text.splitOn "\n"

/-- Assumes one workspace writer. Checks the preimage again before atomic replacement. -/
private def atomicWrite (ctx : ToolContext) (deadline : Nat) (path : String) (bytes : ByteArray)
    (expected : Option String) (overwrite : Bool) (started : IO.Ref Bool) : IO Unit := do
  if bytes.size > maxFileBytes then throw <| IO.userError "new content exceeds file-size limit"
  withParent ctx.workspace path fun parent name => do
    let before ← statAt parent name
    if before.kind != 1 && before.kind != 4 then
      throw <| IO.userError "destination must be a regular file, never a symlink"
    if expected.isNone && !overwrite && before.kind != 4 then
      throw <| IO.userError "destination exists; overwrite is false"
    if let some hash := expected then
      if before.kind == 4 then throw <| IO.userError "edit target no longer exists"
      unless (← sha256 (← readAt parent name)) == hash do
        throw <| IO.userError "preimage changed; read the file again before editing"
    let mode := if before.kind == 1 then before.mode else 420
    ensureActive ctx deadline
    started.set true
    let (temporary, fd) ← mkTempAt parent mode
    try
      try
        Native.write fd bytes
        Native.sync fd
      finally close fd
      ensureActive ctx deadline
      if expected.isNone && !overwrite then
        linkAt parent temporary name
        unlinkAt parent temporary
      else renameAt parent temporary name
      Native.sync parent
    finally
      try unlinkAt parent temporary catch _ => pure ()

private def execute (ctx : ToolContext) (deadline : Nat) (started : IO.Ref Bool)
    (call : ToolCall) : IO ToolResult := do
  ensureActive ctx deadline
  match call.operation with
  | .listFiles args =>
    let paths ← filesUnder ctx deadline args.path
    let text := String.intercalate "\n" (paths.toList.take args.limit)
    boundedResult ctx (text ++ if paths.size > args.limit then
      "\n[file list truncated; choose a narrower path or higher limit]" else "")
  | .readFile args =>
    let bytes ← readFile ctx.workspace args.path
    let hash ← sha256 bytes
    let allLines := lines (← utf8 bytes)
    let selected := (allLines.drop (args.startLine - 1)).take (args.endLine + 1 - args.startLine)
    let numbered := selected.zipIdx args.startLine |>.map fun (line, number) => s!"{number}: {line}\n"
    boundedResult ctx (s!"sha256: {hash}\nlines: {allLines.length}; showing {args.startLine}-{min args.endLine allLines.length}\n" ++
      String.join numbered) (some hash)
  | .searchFiles args =>
    let paths ← searchPaths ctx deadline args.path
    -- Lean lowercasing is ASCII-only; other Unicode codepoints match literally.
    let needle := if args.caseSensitive then args.query else args.query.toLower
    let mut retained := ByteArray.empty
    let mut total := 0
    let mut scanned := 0
    let mut count := 0
    let mut skipped := 0
    for path in paths do
      ensureActive ctx deadline
      let content ← try
        let data ← readFile ctx.workspace path
        scanned := scanned + data.size
        pure (some (← utf8 data))
      catch _ =>
        skipped := skipped + 1
        pure none
      if scanned > 64 * 1024 * 1024 then
        let suffix := "\n[64 MiB scan limit reached; choose a narrower path]"
        return ← boundedResult ctx (utf8Prefix retained retained.size ++ suffix) none (some (total + suffix.utf8ByteSize))
      if let some text := content then
        for (line, number) in (lines text).zipIdx 1 do
          let haystack := if args.caseSensitive then line else line.toLower
          if haystack.contains needle then
            let output := s!"{path}:{number}:{line}\n" |>.toUTF8
            total := total + output.size
            retained := retained ++ output.extract 0 (maxArtifactBytes - retained.size)
            count := count + 1
            if count ≥ args.limit then
              let suffix := "\n[match limit reached]"
              return ← boundedResult ctx (utf8Prefix retained retained.size ++ suffix) none (some (total + suffix.utf8ByteSize))
    let suffix := s!"\n[skipped {skipped} unreadable, oversized, or non-UTF-8 files]"
    boundedResult ctx (utf8Prefix retained retained.size ++ suffix) none (some (total + suffix.utf8ByteSize))
  | .editFile args =>
    let bytes ← readFile ctx.workspace args.path
    unless (← sha256 bytes) == args.expectedSha256 do
      throw <| IO.userError "preimage changed; read the file again before editing"
    let text ← utf8 bytes
    if args.old.isEmpty || (text.splitOn args.old).length != 2 then
      throw <| IO.userError "old must match exactly once; choose a larger unique span"
    let updated := (text.replace args.old args.new).toUTF8
    let hash ← sha256 updated
    ensureActive ctx deadline
    atomicWrite ctx deadline args.path updated (some args.expectedSha256) true started
    return {text := s!"edited {args.path}; sha256: {hash}", sha256 := some hash}
  | .createFile args =>
    let bytes := args.content.toUTF8
    let hash ← sha256 bytes
    atomicWrite ctx deadline args.path bytes none args.overwrite started
    return {text := s!"created {args.path}; sha256: {hash}", sha256 := some hash}
  | .runProcess _ => throw <| IO.userError "process calls belong to ProcessIO"
  | .readArtifact args => ArtifactIO.read ctx args

/-- One typed direct-filesystem operation; the core already chose permission and budget. -/
def run (ctx : ToolContext) (call : ToolCall) : IO (ToolObservation ToolResult) := do
  let localDeadline := (← IO.monoMsNow) + ctx.timeoutMs
  let deadline := min localDeadline (ctx.invocationDeadlineMs.getD localDeadline)
  let started ← IO.mkRef false
  try return .success (← execute ctx deadline started call)
  catch error =>
    if ← started.get then return .uncertain s!"file mutation outcome requires inspection: {error}"
    if (← cancelled ctx) || (← IO.monoMsNow) ≥ deadline then return .interrupted s!"{error}"
    return .failure s!"{error}"

end Harness.FilesystemIO
