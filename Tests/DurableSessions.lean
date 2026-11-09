import Harness.Core.Recovery
import Harness.Applications.Inventory
import Harness.Adapter.ProcessIO
import Harness.Adapter.JournalIO

/-!
Combined release gate against the real CLI: three trusted turns, forced accepted
compactions, process restarts, and a mutation committed before its reply is lost.
Both installed applications use the same scenario. Syscall faults are isolated
to child processes; no production test hook or model credential is involved.
-/
namespace Tests.DurableSessions
open Lean Harness

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError s!"durable session: {label}"

private def response (content : Array Json) (stop : String := "end_turn") : Json :=
  Json.mkObj [("type", toJson "message"), ("role", toJson "assistant"),
    ("content", toJson content), ("stop_reason", toJson stop),
    ("usage", Json.mkObj [("input_tokens", toJson (10 : Nat)), ("output_tokens", toJson (5 : Nat))])]

private def call (id name : String) (fields : List (String × Json)) : Json :=
  Json.mkObj [("type", toJson "tool_use"), ("id", toJson id), ("name", toJson name),
    ("input", Json.mkObj fields)]

private def summary (n : Nat) : Json :=
  response #[textBlock s!"Summary {n}: the mutation committed once. Preserve the task constraints and inspect its current result."]

private def final (n : Nat) : Json := response #[textBlock s!"Completed turn {n}; observed the saved result."]

private def invoke (binary : String) (arguments : Array String) (expected : UInt32 := 0)
    (environment : Option (Array (String × Option String)) := none) : IO String := do
  let result ← ProcessIO.capture {
    cmd := binary, args := arguments, timeoutMs := 60000, cancelPath := "",
    stdoutBytes := 2 * 1024 * 1024, stderrBytes := 65536, includeHome := false, environment}
  let output := String.fromUTF8! result.stdout
  check s!"CLI {arguments.toList}: expected {expected}, got {result.exitCode}; {String.fromUTF8! result.stderr}\n{output}"
    (result.status == .completed && result.exitCode == some expected)
  check "truncated CLI output" (result.stdoutTotal == result.stdout.size)
  return output

private def inspection (binary session : String) : IO Json :=
  return ← IO.ofExcept <| Json.parse (← invoke binary #["inspect", session])

private def savedState (binary session : String) : IO Json :=
  return ← IO.ofExcept <| (← inspection binary session).getObjVal? "state"

private def nat (value : Json) (field : String) : IO Nat :=
  IO.ofExcept <| value.getObjValAs? Nat field

private def writeJson (path : System.FilePath) (value : Json) : IO Unit :=
  IO.FS.writeFile path value.compress

private def environment (shim session mode matchText : String) (skip : Nat := 0) :
    Array (String × Option String) := #[
  ("LD_PRELOAD", some shim), ("HARNESS_JOURNAL_PATH", some (session ++ "/journal.jsonl")),
  ("HARNESS_JOURNAL_FAULT", some mode), ("HARNESS_JOURNAL_MATCH", some matchText),
  ("HARNESS_JOURNAL_SKIP", some (toString skip))]

private def mutation (application sha : String) : Json :=
  if application == "coding" then
    call "mutation" "edit" [("path", toJson "value.txt"), ("old", toJson "before"),
      ("new", toJson "after"), ("expectedSha256", toJson sha)]
  else call "mutation" "reserve" [("sku", toJson "SKU-A"), ("units", toJson (3 : Nat))]

private def query (application id : String) : Json :=
  if application == "coding" then call id "read" [("path", toJson "value.txt")]
  else call id "lookup" [("sku", toJson "SKU-A")]

private def seed : Inventory.Dataset := {version := 1, items := #[
  {sku := "SKU-A", name := "Item A", warehouse := "north", onHand := 10, reorderPoint := 12}]}

private def scenario (base : System.FilePath) (binary shim application : String) : IO Unit := do
  let root := base / application
  let workspace := root / "workspace"
  let session := (root / "session").toString
  IO.FS.createDirAll workspace
  IO.FS.writeFile (workspace / "value.txt") "before\n"
  let sha ← Native.sha256 "before\n".toUTF8
  let script := #[response #[mutation application sha] "tool_use", summary 1, final 0,
    summary 2, response #[query application "query-1"] "tool_use", summary 3, final 1,
    summary 4, response #[query application "query-2"] "tool_use", summary 5, final 2]
  let config := Json.mkObj [("model", toJson "scripted-durable-session"),
    ("instructions", toJson "Preserve the exact user constraints across every turn."),
    ("commands", toJson (if application == "coding" then "deny" else "ask")),
    ("maxModelAttempts", toJson (20 : Nat)),
    ("maxToolCalls", toJson (10 : Nat)), ("maxElapsedMs", toJson (30000 : Nat)),
    ("operationTimeoutMs", toJson (5000 : Nat)), ("maxContextBytes", toJson (100000 : Nat)),
    ("compactAtPercent", toJson (1 : Nat)), ("compactionKeepMessages", toJson (2 : Nat)),
    ("maxSummaryBytes", toJson (2000 : Nat)), ("maxRetries", toJson (0 : Nat))]
  writeJson (root / "config.json") config
  writeJson (root / "script.json") (toJson script)
  writeJson (root / "data.json") (toJson seed)
  let applicationArgs := if application == "coding" then #["--workspace", workspace.toString]
    else #["--data", (root / "data.json").toString]
  let arguments := #["run", "--application", application, "--session", session,
    "--config", (root / "config.json").toString, "--script", (root / "script.json").toString,
    "--task", "Perform the one requested mutation, inspect its outcome, then finish."] ++ applicationArgs
  -- Four completions would be control, model, tool-control, mutation. Stop
  -- before writing the fourth, after the real adapter has committed its effect.
  let _ ← invoke binary arguments 88
    (some (environment shim session "crash_before_write" "\"kind\":\"completion\"" 3))
  let lost ← inspection binary session
  check "mutation intent remains unresolved" ((lost.getObjValAs? Bool "pending").toOption == some true)
  let pending ← IO.ofExcept <| lost.getObjVal? "state"
  check "lost reply preserves reserved budgets" ((← nat pending "modelAttempts") == 1 &&
    (← nat pending "toolDispatches") == 1 && (← nat pending "turn") == 0)
  let before ← IO.FS.readBinFile (session ++ "/journal.jsonl")
  let _ ← invoke binary #["continue", session, "--task", "Do not bypass the unresolved mutation."] 2
  check "rejected follow-up preserves journal" ((← IO.FS.readBinFile (session ++ "/journal.jsonl")) == before)
  let _ ← invoke binary #["resume", session, "--yield-after", "4"] 75
  let _ ← invoke binary #["resume", session]
  let first ← savedState binary session
  check "first turn settled with accounted summary" ((← nat first "turn") == 0 &&
    (← nat first "modelAttempts") == 3 && (← nat first "toolDispatches") == 1)
  let frozen ← IO.ofExcept <| first.getObjVal? "config"
  let mut previous := first
  for turn in [1, 2] do
    let events ← invoke binary #["continue", session, "--task", s!"Follow-up {turn}: inspect the saved mutation without repeating it.", "--json"]
    for line in events.splitOn "\n" do
      unless line.isEmpty do
        let event ← IO.ofExcept <| Json.parse line
        check "event reports authoritative turn" ((← nat event "turn") == turn)
    let current ← savedState binary session
    check "turn increments exactly once" ((← nat current "turn") == turn)
    check "frozen configuration unchanged" ((← IO.ofExcept <| current.getObjVal? "config") == frozen)
    for field in ["nextId", "modelAttempts", "toolDispatches", "knownInputTokens", "knownOutputTokens"] do
      check s!"{field} not refunded" ((← nat previous field) < (← nat current field))
    check "old grant cleared" ((current.getObjVal? "grant").toOption == some Json.null)
    let replay ← IO.ofExcept <| Json.parse (← invoke binary #["replay", session])
    check "offline replay equals inspect" ((← IO.ofExcept <| replay.getObjVal? "state") == current)
    previous := current
  let summaries ← IO.ofExcept <| previous.getObjValAs? (Array Json) "summaries"
  check "accepted repeated compaction" (summaries.size ≥ 2)
  check "all summary attempts counted" ((← nat previous "modelAttempts") == 11 &&
    (← nat previous "toolDispatches") == 3 && (← nat previous "unknownUsage") == 0)
  let records := (← JournalIO.read (session ++ "/journal.jsonl")).records
  check "two durable follow-ups" ((records.filter fun r =>
    (r.getObjValAs? String "kind").toOption == some "user_turn").size == 2)
  check "one recovery resolution" ((records.filter fun r =>
    (r.getObjValAs? String "kind").toOption == some "resolution").size == 1)
  if application == "coding" then
    check "file mutation committed once" ((← IO.FS.readFile (workspace / "value.txt")) == "after\n")
  else
    let ledger := (← JournalIO.read (session ++ "/inventory.jsonl")).records
    check "one stock receipt plus header" (ledger.size == 2)
    let history ← IO.ofExcept <| previous.getObjValAs? (List Harness.Message) "history"
    let mut checked := 0
    for message in history do
      for block in message.content do
        if [some "query-1", some "query-2"].contains
            (block.getObjValAs? String "tool_use_id").toOption then
          let encoded ← IO.ofExcept <| block.getObjValAs? String "content"
          let rendered : ToolResult ← IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse encoded)
          let value ← IO.ofExcept <| Json.parse rendered.text
          let item ← IO.ofExcept <| value.getObjValAs? Inventory.Item "item"
          check "query observed debited stock" (item.sku == "SKU-A" && item.onHand == 7)
          checked := checked + 1
    check "both later queries independently checked" (checked == 2)
  IO.println s!"{application}: three turns, {summaries.size} compactions, lost mutation reply, restart and replay passed."

private def cancellationScenario (base : System.FilePath) (binary shim application : String) : IO Unit := do
  let root := base / application
  let session := (root / "cancelled-session").toString
  let oldConfig ← IO.ofExcept <| Json.parse (← IO.FS.readFile (root / "config.json"))
  writeJson (root / "cancel-config.json")
    (oldConfig.mergeObj (Json.mkObj [("compactionEnabled", toJson false)]))
  writeJson (root / "cancel-script.json") (toJson #[
    response #[query application "skipped-1", query application "skipped-2"] "tool_use",
    final 1, final 2])
  let applicationArgs := if application == "coding" then #["--workspace", (root / "workspace").toString]
    else #["--data", (root / "data.json").toString]
  let _ ← invoke binary (#["run", "--application", application, "--session", session,
    "--config", (root / "cancel-config.json").toString,
    "--script", (root / "cancel-script.json").toString,
    "--task", "Inspect both requested items.", "--yield-after", "2"] ++ applicationArgs) 75
  let _ ← invoke binary #["cancel", session]
  let _ ← invoke binary #["resume", session] 130
  let cancelled ← savedState binary session
  let history ← IO.ofExcept <| cancelled.getObjValAs? (List Harness.Message) "history"
  check "cancelled batch is protocol-closed" (historyValid history)
  check "cancelled calls never dispatched" ((← nat cancelled "toolDispatches") == 0)
  let resultIds := history.flatMap fun message => message.content.toList.filterMap fun block =>
    (block.getObjValAs? String "tool_use_id").toOption
  check "cancelled suffix has exactly ordered results" (resultIds == ["skipped-1", "skipped-2"])
  let before ← IO.FS.readBinFile (session ++ "/journal.jsonl")
  let _ ← invoke binary #["continue", session, "--task", "Storage failure must not start this turn."] 2
    (some (environment shim session "before_write" "\"kind\":\"user_turn\""))
  check "failed turn append leaves state unchanged" ((← savedState binary session) == cancelled)
  check "failed turn append leaves prefix unchanged" ((← IO.FS.readBinFile (session ++ "/journal.jsonl")) == before)
  let _ ← invoke binary #["continue", session, "--task", "Start a new bounded turn.", "--yield-after", "1"] 75
  let admitted ← savedState binary session
  check "old cancellation did not cancel follow-up" ((← nat admitted "turn") == 1 &&
    (← nat admitted "modelAttempts") == 2)
  check "old marker retained" (← (System.FilePath.mk (session ++ "/cancel")).pathExists)
  let _ ← invoke binary #["cancel", session]
  check "new cancellation targets new turn" (← (System.FilePath.mk (session ++ "/cancel.1")).pathExists)
  let _ ← invoke binary #["resume", session] 130
  let freshCancelled ← savedState binary session
  check "reserved interrupted request remains charged" ((← nat freshCancelled "modelAttempts") == 2 &&
    (← nat freshCancelled "unknownUsage") == 1)
  let _ ← invoke binary #["continue", session, "--task", "Finish after acknowledging the cancelled turn."]
  let finalState ← savedState binary session
  check "third turn keeps cumulative accounting" ((← nat finalState "turn") == 2 &&
    (← nat finalState "modelAttempts") == 3 && (← nat finalState "unknownUsage") == 1 &&
    (← nat finalState "toolDispatches") == 0)
  IO.println s!"{application}: cancellation settlement, turn-scoped markers and failed turn persistence passed."

def run (base : System.FilePath) : IO Unit := do
  let binary := ((← IO.currentDir) / ".lake/build/bin/harness").toString
  let shim := base / "faults.so"
  let compiled ← IO.Process.output {cmd := "rustc", args := #["--crate-type", "cdylib", "--edition=2021",
    "-C", "opt-level=1", "-D", "warnings", "-o", shim.toString, "Tests/journal_writer_faults.rs"]}
  check s!"compile fault shim: {compiled.stderr}" (compiled.exitCode == 0)
  for application in ["coding", "inventory"] do
    scenario base binary shim.toString application
    cancellationScenario base binary shim.toString application

end Tests.DurableSessions

def main : IO UInt32 := do
  let base := System.FilePath.mk s!"/tmp/lean-harness-durable-{← IO.monoNanosNow}"
  IO.FS.createDir base
  try
    Tests.DurableSessions.run base
    IO.FS.removeDirAll base
    return 0
  catch error =>
    IO.eprintln s!"{error}\nEvidence retained at {base}"
    return 1
