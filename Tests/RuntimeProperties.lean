import Plausible.Gen
import Harness.Adapter.FilesystemIO
import Harness.Adapter.JournalIO
import Tests.RecoveryProperties

/-! Generated IO tests, not theorem declarations. Plausible supplies bounded Unicode
inputs and operation sequences from fixed seeds. An independent four-file model and
record list predict effects; Lean's standard filesystem API checks the bytes, and the
test-only sha256sum command checks digests. Sequence failures report their seed and
undergo bounded deletion shrinking in fresh fixtures. All temporary files are removed. -/
open Lean Harness Plausible

private def alphabet : Array Char := #['a', 'Z', '0', ' ', '\n', '\r', '\t', '\"', '\\',
  'λ', '🙂', 'ß', 'é', '界', '\x00', '́']

private def sampleText : Gen String := do
  let count ← Gen.chooseNat
  let mut chars := []
  for _ in [:count] do
    let index ← Gen.choose Nat 0 (alphabet.size - 1) (by decide)
    chars := alphabet[index.val]! :: chars
  return String.ofList chars.reverse

private def generate (seed : Nat) : IO (String × String) := do
  let sample : Gen (String × String) := do return (← sampleText, ← sampleText)
  match (Plausible.runRandWith seed sample).run ⟨32⟩ with
  | .ok value => pure value
  | .error error => throw <| Gen.genFailure error

private def check (seed : Nat) (label : String) (holds : Bool) : IO Unit :=
  unless holds do throw <| IO.userError s!"IO property seed={seed}: {label}"

private def success (seed : Nat) (label : String) : ToolObservation ToolResult → IO ToolResult
  | .success result => pure result
  | other => throw <| IO.userError s!"IO property seed={seed}: {label}: {(toJson other).compress}"

private def failed : ToolObservation ToolResult → Bool
  | .failure _ => true
  | _ => false

private def checksum (path : String) : IO String := do
  let result ← IO.Process.output {cmd := "sha256sum", args := #[path]}
  if result.exitCode != 0 then throw <| IO.userError "test-only sha256sum oracle failed"
  return (result.stdout.splitOn " ").head!

private def testCase (base : String) (seed : Nat) (source replacement : String) : IO Unit := do
  let workspace := base ++ "/workspace"
  Native.mkdir workspace 448
  let context : ToolContext := {
    workspace, timeoutMs := 30000, outputBytes := 65536,
    artifactDir := base ++ "/artifacts", cancelPath := base ++ "/cancel" }
  let original := source ++ "\n@@ONE@@\n"
  let path := workspace ++ "/sample.txt"
  let created ← FilesystemIO.run context {id := "create", operation := .createFile {path := "sample.txt", content := original}}
  let createResult ← success seed "create" created
  check seed "create bytes differ from generated text" ((← IO.FS.readBinFile path) == original.toUTF8)
  let originalHash ← checksum path
  check seed "create SHA256 differs from independent oracle" (createResult.sha256 == some originalHash)
  let read ← FilesystemIO.run context {id := "read", operation := .readFile {path := "sample.txt"}}
  let readResult ← success seed "read" read
  check seed "read SHA256 differs from independent oracle" (readResult.sha256 == some originalHash)
  let edit : ToolCall := {id := "edit", operation := .editFile {
    path := "sample.txt", old := "@@ONE@@", new := replacement, expectedSha256 := originalHash}}
  let edited ← success seed "exact edit" (← FilesystemIO.run context edit)
  let expected := source ++ "\n" ++ replacement ++ "\n"
  check seed "edit bytes differ from independently constructed result" ((← IO.FS.readBinFile path) == expected.toUTF8)
  check seed "edit SHA256 differs from independent oracle" (edited.sha256 == some (← checksum path))
  let stale ← FilesystemIO.run context edit
  check seed "stale edit was not rejected" (failed stale)
  check seed "stale edit changed bytes" ((← IO.FS.readBinFile path) == expected.toUTF8)
  let ambiguous := source ++ "@@ONE@@" ++ replacement ++ "@@ONE@@"
  IO.FS.writeBinFile path ambiguous.toUTF8
  let ambiguousHash ← checksum path
  let ambiguousEdit : ToolCall := {id := "ambiguous", operation := .editFile {
    path := "sample.txt", old := "@@ONE@@", new := "replacement", expectedSha256 := ambiguousHash}}
  check seed "ambiguous edit was not rejected" (failed (← FilesystemIO.run context ambiguousEdit))
  check seed "ambiguous edit changed bytes" ((← IO.FS.readBinFile path) == ambiguous.toUTF8)
  let outside := base ++ "/outside.txt"
  let sentinel := "outside workspace: " ++ source
  IO.FS.writeBinFile outside sentinel.toUTF8
  for candidatePath in ["../outside.txt", "./../outside.txt", "nested/../../outside.txt", outside] do
    let rejected ← FilesystemIO.run context {id := "escape", operation := .createFile {path := candidatePath, content := replacement, overwrite := true}}
    check seed s!"unsafe path accepted: {candidatePath}" (failed rejected)
    check seed "unsafe path changed outside file" ((← IO.FS.readBinFile outside) == sentinel.toUTF8)
  let symlink ← IO.Process.output {cmd := "ln", args := #["-s", outside, workspace ++ "/link"]}
  check seed "symlink fixture creation failed" (symlink.exitCode == 0)
  check seed "symlink overwrite accepted" (failed (← FilesystemIO.run context
    {id := "symlink", operation := .createFile {path := "link", content := replacement, overwrite := true}}))
  check seed "symlink overwrite changed outside file" ((← IO.FS.readBinFile outside) == sentinel.toUTF8)
  let journal := base ++ "/journal.jsonl"
  let first := Json.mkObj [("seed", toJson seed), ("text", toJson source)]
  let second := Json.mkObj [("nested", Json.arr #[toJson replacement, toJson source]), ("null", Json.null)]
  JournalIO.append journal first
  let prefixBytes ← IO.FS.readBinFile journal
  JournalIO.append journal second
  let history ← JournalIO.read journal
  check seed "journal did not preserve generated records" (history.records == #[first, second] && !history.interrupted)
  let completeBytes ← IO.FS.readBinFile journal
  let remove := 1 + seed % (min 16 (completeBytes.size - prefixBytes.size))
  let tornBytes := completeBytes.extract 0 (completeBytes.size - remove)
  IO.FS.writeBinFile journal tornBytes
  let torn ← JournalIO.read journal
  check seed "torn journal did not preserve exactly the completed prefix" (torn.records == #[first] && torn.interrupted)
  let refused ← try JournalIO.append journal second; pure false catch _ => pure true
  check seed "append to torn journal was accepted" refused
  check seed "refused journal append changed evidence" ((← IO.FS.readBinFile journal) == tornBytes)

private def searchCase (root : String) : IO Unit := do
  let context : ToolContext := {
    workspace := root, timeoutMs := 30000, outputBytes := 65536,
    artifactDir := root ++ "/artifacts", cancelPath := root ++ "/cancel" }
  IO.FS.writeFile (root ++ "/case.txt") "Straße\nHELLO\n"
  let ascii ← success 0 "ASCII insensitive search" (← FilesystemIO.run context
    {id := "ascii", operation := .searchFiles {path := "case.txt", query := "hello", caseSensitive := false}})
  check 0 "ASCII case-insensitive matching failed" (ascii.text.contains "HELLO")
  let unicode ← success 0 "Unicode literal search" (← FilesystemIO.run context
    {id := "unicode", operation := .searchFiles {path := "case.txt", query := "STRASSE", caseSensitive := false}})
  check 0 "ASCII mode unexpectedly claimed full Unicode casefold" (!(unicode.text.contains "Straße"))

private inductive FileAction where
  | create | overwrite | read | edit | stale | ambiguous | externalWrite
  | cancelRead | cancelWrite | unsafeWrite | append | save | replay | torn
  deriving Repr, Inhabited, BEq

private def actions : Array FileAction := #[.create, .overwrite, .read, .edit, .stale,
  .ambiguous, .externalWrite, .cancelRead, .cancelWrite, .unsafeWrite, .append,
  .save, .replay, .torn]

private def actionName : FileAction → String
  | .create => "create" | .overwrite => "overwrite" | .read => "read"
  | .edit => "edit" | .stale => "stale" | .ambiguous => "ambiguous"
  | .externalWrite => "externalWrite" | .cancelRead => "cancelRead"
  | .cancelWrite => "cancelWrite" | .unsafeWrite => "unsafeWrite"
  | .append => "append" | .save => "save" | .replay => "replay" | .torn => "torn"

private structure Operation where
  action : FileAction
  file : Nat
  text : String
  deriving Repr, Inhabited

private structure Model where
  files : Array (Option String) := #[none, none, none, none]
  remembered : Array (Option String) := #[none, none, none, none]
  records : Array Json := #[]
  saved : ByteArray × Array Json := (ByteArray.empty, #[])

private abbrev Coverage := Array (String × Nat)

private def hit (coverage : IO.Ref Coverage) (label : String) : IO Unit :=
  coverage.modify fun counts =>
    match counts.findIdx? (·.1 == label) with
    | some i => counts.set! i (label, counts[i]!.2 + 1)
    | none => counts.push (label, 1)

private def generateSequence (seed length : Nat) : IO (Array Operation) := do
  let sample : Gen (Array Operation) := do
    let mut ops := #[]
    for _ in [:length] do
      let action ← Gen.choose Nat 0 13 (by decide)
      let file ← Gen.choose Nat 0 3 (by decide)
      ops := ops.push {action := actions[action.val]!, file := file.val, text := ← sampleText}
    return ops
  match (Plausible.runRandWith seed sample).run ⟨12⟩ with
  | .ok value => pure value
  | .error error => throw <| Gen.genFailure error

private def verifyFiles (seed : Nat) (base workspace : String) (model : Model) : IO Unit := do
  for i in [:4] do
    let path := workspace ++ s!"/file{i}.txt"
    match model.files[i]! with
    | none => check seed s!"unexpected file {i}" (!(← (System.FilePath.mk path).pathExists))
    | some text =>
      check seed s!"file {i} differs from model" ((← IO.FS.readBinFile path) == text.toUTF8)
  check seed "outside sentinel changed" ((← IO.FS.readFile (base ++ "/outside")) == "unchanged")

private def observe (seed : Nat) (coverage : IO.Ref Coverage) (expected : String)
    (observation : ToolObservation ToolResult) : IO (Option ToolResult) := do
  let (actual, result) := match observation with
    | .success value => ("success", some value)
    | .failure _ => ("failure", none)
    | .interrupted _ _ => ("interrupted", none)
    | .uncertain _ _ => ("uncertain", none)
    | .timedOut _ => ("timedOut", none)
  check seed s!"expected {expected}, got {(toJson observation).compress}" (expected == actual)
  hit coverage ("outcome." ++ actual)
  return result

/-- The reference map changes only by the independently specified operation, never
by decoding tool output. Every operation checks all four files and the outside sentinel. -/
private def runSequence (base : String) (seed : Nat) (ops : Array Operation)
    (coverage : IO.Ref Coverage) : IO Unit := do
  Native.mkdir base 448
  try
    let workspace := base ++ "/workspace"
    Native.mkdir workspace 448
    IO.FS.writeFile (base ++ "/outside") "unchanged"
    let ctx : ToolContext := {
      workspace, timeoutMs := 30000, outputBytes := 65536,
      artifactDir := base ++ "/artifacts", cancelPath := base ++ "/cancel" }
    let journal := base ++ "/journal"
    IO.FS.writeBinFile journal ByteArray.empty
    let mut model : Model := {}
    for (op, position) in ops.toList.zipIdx do
      hit coverage s!"action.{actionName op.action}"
      let path := s!"file{op.file}.txt"
      let absolute := workspace ++ "/" ++ path
      let content := "value:" ++ op.text ++ "\n"
      let invoke := fun operation => FilesystemIO.run ctx {id := s!"{position}", operation}
      match op.action with
      | .create | .overwrite =>
        let overwrite := op.action == .overwrite
        let accepted := overwrite || model.files[op.file]!.isNone
        let result ← invoke (.createFile {path, content, overwrite})
        let _ ← observe seed coverage (if accepted then "success" else "failure") result
        if accepted then model := {model with files := model.files.set! op.file (some content)}
      | .read =>
        let expected := if model.files[op.file]!.isSome then "success" else "failure"
        if let some result ← observe seed coverage expected (← invoke (.readFile {path})) then
          let digest ← checksum absolute
          check seed "read returned an incorrect preimage digest" (result.sha256 == some digest)
          model := {model with remembered := model.remembered.set! op.file (some digest)}
      | .edit =>
        let present := model.files[op.file]!
        let digest ← if present.isSome then checksum absolute else pure (String.ofList (List.replicate 64 '0'))
        let observation ← invoke (.editFile {path, old := present.getD "absent", new := content, expectedSha256 := digest})
        let _ ← observe seed coverage (if present.isSome then "success" else "failure") observation
        if present.isSome then model := {model with files := model.files.set! op.file (some content)}
      | .stale =>
        let current ← if model.files[op.file]!.isSome then checksum absolute else pure ""
        let remembered := model.remembered[op.file]!.getD ""
        let stale := if !remembered.isEmpty && remembered != current then remembered
          else String.ofList (List.replicate 64 '0')
        if !remembered.isEmpty && remembered != current then hit coverage "preimage.rememberedStale"
        let observation ← invoke (.editFile {path, old := "value:", new := content, expectedSha256 := stale})
        let _ ← observe seed coverage "failure" observation
        if model.files[op.file]!.isSome then
          match observation with
          | .failure message => check seed "stale edit did not fail its preimage check" (message.contains "preimage")
          | _ => pure ()
        hit coverage "rejection.stale"
      | .ambiguous =>
        let duplicated := "@match@" ++ op.text ++ "@match@"
        IO.FS.writeFile absolute duplicated
        model := {model with files := model.files.set! op.file (some duplicated)}
        let observation ← invoke (.editFile {path, old := "@match@", new := content, expectedSha256 := ← checksum absolute})
        let _ ← observe seed coverage "failure" observation
        hit coverage "rejection.ambiguous"
      | .externalWrite =>
        IO.FS.writeFile absolute content
        model := {model with files := model.files.set! op.file (some content)}
      | .cancelRead | .cancelWrite =>
        IO.FS.writeFile ctx.cancelPath "cancel"
        try
          let operation := if op.action == .cancelRead then .readFile {path}
            else .createFile {path, content, overwrite := true}
          let _ ← observe seed coverage "interrupted" (← invoke operation)
          pure ()
        finally IO.FS.removeFile ctx.cancelPath
      | .unsafeWrite =>
        let candidatePath := if op.file % 2 == 0 then "../outside" else base ++ "/outside"
        let _ ← observe seed coverage "failure" (← invoke (.createFile {path := candidatePath, content, overwrite := true}))
        hit coverage "rejection.unsafePath"
      | .append =>
        let record := Json.mkObj [("sequence", toJson position), ("text", toJson op.text)]
        JournalIO.append journal record
        model := {model with records := model.records.push record}
        let actual ← JournalIO.read journal
        check seed "append changed journal record order or value" (actual.records == model.records && !actual.interrupted)
      | .save =>
        model := {model with saved := (← IO.FS.readBinFile journal, model.records)}
      | .replay =>
        -- Replay only a saved complete prefix into a fresh file. No effects are rerun.
        let copy := base ++ "/saved-prefix"
        IO.FS.writeBinFile copy model.saved.1
        let result ← JournalIO.read copy
        check seed "saved completed prefix reconstructed different records" (result.records == model.saved.2 && !result.interrupted)
        if !model.saved.2.isEmpty then hit coverage "replay.nonemptySavedPrefix"
      | .torn =>
        let copy := base ++ "/torn-prefix"
        let bytes := (← IO.FS.readBinFile journal) ++ "{incomplete".toUTF8
        IO.FS.writeBinFile copy bytes
        let result ← JournalIO.read copy
        check seed "torn tail changed completed journal prefix" (result.records == model.records && result.interrupted)
        let refused ← try JournalIO.append copy (toJson op.text); pure false catch _ => pure true
        check seed "append accepted a torn tail" refused
        check seed "rejected append changed torn evidence" ((← IO.FS.readBinFile copy) == bytes)
        hit coverage "rejection.tornAppend"
      verifyFiles seed base workspace model
  finally IO.FS.removeDirAll base

/-- Bounded deletion shrinking reruns every candidate in a new directory. This is
test-only trace minimization; no production transition or failure is discarded. -/
private def shrinkSequence (root : String) (seed : Nat) (ops : Array Operation) : IO (Array Operation) := do
  let mut reduced := ops
  let mut offset := 0
  for attempt in [:min 200 (ops.size * 2)] do
    if offset ≥ reduced.size then break
    let candidate := reduced.extract 0 offset ++ reduced.extract (offset + 1) reduced.size
    let coverage ← IO.mkRef (#[] : Coverage)
    let fails ← try
      runSequence (root ++ s!"/shrink-{seed}-{attempt}") seed candidate coverage
      pure false
    catch _ => pure true
    if fails then reduced := candidate else offset := offset + 1
  return reduced

private def setting (name : String) (fallback maximum : Nat) : IO Nat := do
  match ← IO.getEnv name with
  | none => pure fallback
  | some value =>
    match value.toNat? with
    | some count =>
      if count == 0 || count > maximum then throw <| IO.userError s!"{name} must be in 1..{maximum}"
      pure count
    | none => throw <| IO.userError s!"{name} must be a natural number"

private def statefulCases (root : String) : IO Unit := do
  let count ← setting "HARNESS_IO_SEQUENCES" 200 10000
  let length ← setting "HARNESS_IO_SEQUENCE_LENGTH" 30 200
  let firstSeed ← setting "HARNESS_IO_START_SEED" 61000 1000000000
  let coverage ← IO.mkRef (#[] : Coverage)
  for seed in [firstSeed:firstSeed + count] do
    let ops ← generateSequence seed length
    try runSequence (root ++ s!"/sequence-{seed}") seed ops coverage
    catch error =>
      let reduced ← shrinkSequence root seed ops
      throw <| IO.userError s!"{error}\nseed={seed}; deletion-shrunk operations={repr reduced}"
  let counts := (← coverage.get).qsort (fun a b => a.1 < b.1)
  -- Small explicitly requested diagnostic runs need not cover every operation.
  if count ≥ 200 && length ≥ 30 then
    for action in actions do
      check 0 s!"generated suite did not exercise {actionName action}" (counts.any (·.1 == s!"action.{actionName action}"))
    for label in ["outcome.success", "outcome.failure", "outcome.interrupted", "rejection.stale",
        "rejection.ambiguous", "rejection.unsafePath", "rejection.tornAppend",
        "preimage.rememberedStale", "replay.nonemptySavedPrefix"] do
      check 0 s!"generated suite did not exercise {label}" (counts.any (·.1 == label))
  IO.println s!"Stateful IO: {count} sequences × {length} operations passed (seeds {firstSeed}–{firstSeed + count - 1}); coverage: {repr counts}"

/-- The cases execute real IO and throw on failure; no plausible tactic enters a proof. -/
def main : IO Unit := do
  Native.installSignals
  let root := s!"/tmp/lean-harness-io-properties-{← Native.getPid}-{← IO.monoNanosNow}"
  Native.mkdir root 448
  try
    searchCase root
    for seed in [52000:52100] do
      let (source, replacement) ← generate seed
      let directory := root ++ s!"/{seed}"
      Native.mkdir directory 448
      try testCase directory seed source replacement
      catch error => throw <| IO.userError s!"{error}\nsource={repr source}\nreplacement={repr replacement}"
    IO.println "IO properties: 100 Plausible-generated filesystem/journal cases passed (seeds 52000–52099); ASCII search contract passed"
    statefulCases root
    Tests.RecoveryProperties.run root
  finally IO.FS.removeDirAll root
