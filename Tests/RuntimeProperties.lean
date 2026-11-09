import Plausible.Gen
import Harness.Adapter.FilesystemIO
import Harness.Adapter.JournalIO

/-! Generated IO tests, not theorem declarations. Plausible supplies bounded Unicode
inputs from fixed seeds. The oracle reads final bytes independently through Lean's
standard filesystem API; the test-only sha256sum command independently checks digests.
Each failing case reports its seed and input. All temporary files are removed. -/
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
  for alias in ["../outside.txt", "./../outside.txt", "nested/../../outside.txt", outside] do
    let rejected ← FilesystemIO.run context {id := "escape", operation := .createFile {path := alias, content := replacement, overwrite := true}}
    check seed s!"unsafe path accepted: {alias}" (failed rejected)
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
  finally IO.FS.removeDirAll root
