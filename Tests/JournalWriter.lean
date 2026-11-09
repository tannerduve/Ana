import Harness.Adapter.JournalIO

/-! Real cursor-writer boundary tests and optional increasing-size benchmark.
Faults are injected in child processes by the test-only syscall shim, never by
production flags. Benchmark timings cover fsync, and memory is the worker RSS. -/
open Lean Harness

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError s!"journal writer: {name}"

private def refused (action : IO α) : IO Bool := do
  try let _ ← action; return false
  catch _ => return true

private def record (n : Nat) : Json := Json.mkObj [("record", toJson n)]

private def verify (path : String) (count : Nat) : IO JournalIO.ReadResult := do
  let loaded ← JournalIO.read path
  check "complete frame count" (!loaded.interrupted && loaded.records.size == count)
  check "cursor agrees with count and bytes" (loaded.cursor.sequence == count &&
    loaded.cursor.bytes == (← IO.FS.readBinFile path).size && loaded.cursor.checksum == loaded.checksum)
  return loaded

private def probe (path : String) : IO Unit := do
  JournalIO.withWriter path fun writer _ => do
    let first ← refused <| writer.append (Json.mkObj [("faultTarget", toJson true)])
    let second ← refused <| writer.append (record 999)
    IO.println (Json.mkObj [("firstRefused", toJson first), ("secondRefused", toJson second),
      ("head", toJson (← writer.cursor?))]).compress

private def ordinary (base : System.FilePath) : IO Unit := do
  let path := (base / "journal.jsonl").toString
  let escaped ← JournalIO.withWriter path fun writer initial => do
    check "empty initial" (initial.records.isEmpty && initial.cursor == {})
    for n in [:20] do writer.append (record n)
    let loaded ← verify path 20
    check "retained cursor equals independent revalidation" ((← writer.cursor?) == some loaded.cursor)
    return writer
  check "closed handle refuses" (← refused <| escaped.append (record 21))
  JournalIO.withWriter path fun writer initial => do
    check "reopened count" (initial.cursor.sequence == 20)
    writer.append (record 20)
  let _ ← verify path 21
  let original ← IO.FS.readBinFile path
  JournalIO.withWriter path fun writer _ => do
    let value ← IO.ofExcept <| Json.parse "{\"number\":1.0}"
    check "lossy JSON refused" (← refused <| writer.append value)
    check "failed append poisons handle" ((← writer.cursor?).isNone)
    check "poisoned handle cannot retry" (← refused <| writer.append (record 22))
  check "prewrite rejection retains prefix" ((← IO.FS.readBinFile path) == original)
  for damaged in [original ++ "{torn".toUTF8,
      (String.fromUTF8! original |>.replace "\"checksum\":\"" "\"checksum\":\"bad").toUTF8] do
    IO.FS.writeBinFile path damaged
    let reached ← IO.mkRef false
    check "invalid prefix refuses open" (← refused <| JournalIO.withWriter path fun _ _ => reached.set true)
    check "invalid prefix callback absent" (!(← reached.get))
    check "invalid prefix unchanged" ((← IO.FS.readBinFile path) == damaged)
  IO.FS.writeBinFile path original
  JournalIO.withWriter path fun writer _ => do
    IO.FS.writeBinFile path (original ++ "x".toUTF8)
    check "size drift refuses" (← refused <| writer.append (record 22))
    check "size drift poisons" ((← writer.cursor?).isNone)
  IO.FS.writeBinFile path original
  JournalIO.withWriter path fun writer _ => do
    IO.FS.writeBinFile (base / "replacement") original
    IO.FS.rename (base / "replacement") path
    check "same-size replacement refuses" (← refused <| writer.append (record 22))
  check "replacement unchanged" ((← IO.FS.readBinFile path) == original)
  let before := (← (System.FilePath.mk "/proc/self/fd").readDir).size
  check "callback failure propagated" (← refused <| JournalIO.withWriter path fun _ _ =>
    (throw <| IO.userError "callback" : IO Unit))
  check "callback exception closes descriptors" ((← (System.FilePath.mk "/proc/self/fd").readDir).size == before)
  IO.println "Journal writer ordinary boundaries passed."

private def faults (base : System.FilePath) : IO Unit := do
  let shim := base / "faults.so"
  let compiled ← IO.Process.output {cmd := "rustc", args := #["--crate-type", "cdylib", "--edition=2021",
    "-C", "opt-level=1", "-D", "warnings", "-o", shim.toString, "Tests/journal_writer_faults.rs"]}
  check s!"compile fault shim: {compiled.stderr}" (compiled.exitCode == 0)
  let executable ← IO.appPath
  for mode in ["before_write", "partial", "file_sync", "directory_sync", "crash_partial", "crash_after_sync", "crash_before_write", "no_reads"] do
    let directory := base / mode
    IO.FS.createDir directory
    let path := (directory / "journal.jsonl").toString
    JournalIO.append path (record 0)
    let before ← IO.FS.readBinFile path
    let child ← IO.Process.output {
      cmd := executable.toString
      args := #["--probe", path]
      env := #[("LD_PRELOAD", some shim.toString), ("HARNESS_JOURNAL_FAULT", some mode),
        ("HARNESS_JOURNAL_PATH", some path)]}
    if mode.startsWith "crash_" then
      check s!"{mode} exit" (child.exitCode == if mode == "crash_partial" then 86 else if mode == "crash_after_sync" then 87 else 88)
    else
      check s!"{mode} probe exit: {child.stderr}" (child.exitCode == 0)
      let output ← IO.ofExcept <| Json.parse child.stdout
      let expected := mode != "no_reads"
      check s!"{mode} first outcome" ((output.getObjValAs? Bool "firstRefused").toOption == some expected)
      check s!"{mode} second outcome" ((output.getObjValAs? Bool "secondRefused").toOption == some expected)
      if expected then check s!"{mode} poison" ((output.getObjVal? "head").toOption == some Json.null)
    let after ← IO.FS.readBinFile path
    check s!"{mode} keeps previous bytes" (after.extract 0 before.size == before)
    if mode == "partial" || mode == "crash_partial" then
      let loaded ← JournalIO.read path
      check s!"{mode} torn detected" (loaded.interrupted && loaded.records.size == 1)
      check s!"{mode} reopen refused" (← refused <| JournalIO.withWriter path fun _ _ => pure ())
      check s!"{mode} torn bytes preserved" ((← IO.FS.readBinFile path) == after)
    else
      let count := if mode == "before_write" || mode == "crash_before_write" then 1 else if mode == "no_reads" then 3 else 2
      let _ ← verify path count
      JournalIO.withWriter path fun writer initial => do
        check s!"{mode} reopened head" (initial.cursor.sequence == count)
        writer.append (record 1000)
      let _ ← verify path (count + 1)
      if mode == "before_write" || mode == "crash_before_write" then check "failed write unchanged" (after == before)
    IO.println s!"Journal writer fault {mode} passed."

private def memory : IO Json := do
  let text ← IO.FS.readFile "/proc/self/status"
  let mut fields := []
  for line in text.splitOn "\n" do
    if line.startsWith "VmRSS:" || line.startsWith "VmHWM:" then
      fields := fields ++ [(line.takeWhile (· != ':') |>.toString, toJson line)]
  return Json.mkObj fields

private def median (values : Array Nat) : Nat :=
  let sorted := values.toList.mergeSort (· ≤ ·)
  sorted[sorted.length / 2]!

/-- Fill and measure real fsynced appends at increasing sizes. Historical one-shot
append remains the reference comparison; startup/reopen validation is timed apart. -/
private def benchmark (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  let path := (directory / "journal.jsonl").toString
  check "benchmark requires fresh path" (!(← (System.FilePath.mk path).pathExists))
  let payload := String.ofList (List.replicate (1024 * 1024) 'x')
  let small := Json.mkObj [("payload", toJson (String.ofList (List.replicate 1024 'y')))]
  let mut measurements := #[]
  let started ← IO.monoNanosNow
  JournalIO.withWriter path fun writer _ => do
    for mib in [1, 16, 60] do
      for _ in [:64] do
        let some cursor ← writer.cursor? | throw <| IO.userError "benchmark cursor invalid"
        if cursor.bytes ≥ mib * 1024 * 1024 then break
        writer.append (Json.mkObj [("payload", toJson payload)])
      let size := (← (System.FilePath.mk path).metadata).byteSize
      let mut times := #[]
      for _ in [:16] do
        let tick ← IO.monoNanosNow
        writer.append small
        times := times.push ((← IO.monoNanosNow) - tick)
      IO.println (Json.mkObj [("mode", toJson "retained"), ("journalBytes", toJson size),
        ("appendNanoseconds", toJson times), ("medianNanoseconds", toJson (median times)),
        ("memory", ← memory)]).compress
  let retainedNanos := (← IO.monoNanosNow) - started
  -- Reopen once, then compare retained and safe one-shot appends at this size.
  let reopenStart ← IO.monoNanosNow
  let loaded ← JournalIO.read path
  let reopenNanos := (← IO.monoNanosNow) - reopenStart
  for _ in [:3] do
    let tick ← IO.monoNanosNow
    JournalIO.append path small
    measurements := measurements.push ((← IO.monoNanosNow) - tick)
  let before ← IO.FS.readBinFile path
  let refusedQuota ← refused <| JournalIO.withWriter path fun writer _ =>
    writer.append (Json.mkObj [("payload", toJson (String.ofList (List.replicate (5 * 1024 * 1024) 'z')))])
  check "quota refuses" refusedQuota
  check "quota leaves prefix unchanged" ((← IO.FS.readBinFile path) == before)
  IO.println (Json.mkObj [("mode", toJson "reopen-and-one-shot"),
    ("prefixFrames", toJson loaded.records.size), ("prefixBytes", toJson loaded.cursor.bytes),
    ("fillAndRetainedNanoseconds", toJson retainedNanos), ("readValidateNanoseconds", toJson reopenNanos),
    ("oneShotAppendNanoseconds", toJson measurements), ("memory", ← memory),
    ("quotaRefusedUnchanged", toJson true)]).compress

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["--probe", path] => probe path
    | ["--benchmark", path] => benchmark path
    | [] =>
      let root := System.FilePath.mk s!"/tmp/lean-harness-journal-writer-{← Native.getPid}-{← IO.monoNanosNow}"
      IO.FS.createDir root
      try ordinary root; faults root
      finally IO.FS.removeDirAll root
    | _ => throw <| IO.userError "usage: journal_writer_contracts [--benchmark NEW_DIRECTORY]"
    return 0
  catch error => IO.eprintln (toString error); return 1
