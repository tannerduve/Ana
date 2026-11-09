import Harness.Core.Recovery
import Harness.Applications.Inventory
import Harness.Adapter.ProcessIO
import Harness.Adapter.JournalIO

/-!
Real CLI contracts for the inventory application. A scripted provider controls proposals; actual
Lean queries read admitted local data. Separate CLI processes exercise snapshotting, dependent
journal decoding, resumable execution and lost-query recovery. No credentials or Python are used.
-/
namespace Tests.ApplicationRuntime
open Lean Harness

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError s!"application contract: {label}"

private def jsonFile (path : System.FilePath) (value : Json) : IO Unit :=
  IO.FS.writeFile path value.compress

private def item (sku warehouse : String) (stock target : Nat) : Json := Json.mkObj [
  ("sku", toJson sku), ("name", toJson s!"Item {sku}"), ("warehouse", toJson warehouse),
  ("onHand", toJson stock), ("reorderPoint", toJson target)]

private def data (northStock : Nat := 1) : Json := Json.mkObj [
  ("version", toJson (1 : Nat)), ("items", toJson #[
    item "N1" "north" northStock 10, item "N2" "north" 7 10, item "S1" "south" 5 6])]

private def call (id name : String) (args : Json) : Json := Json.mkObj [
  ("type", toJson "tool_use"), ("id", toJson id), ("name", toJson name), ("input", args)]

private def response (blocks : Array Json) (stop : String) : Json := Json.mkObj [
  ("type", toJson "message"), ("role", toJson "assistant"), ("stop_reason", toJson stop),
  ("content", toJson blocks),
  ("usage", Json.mkObj [("input_tokens", toJson (10 : Nat)), ("output_tokens", toJson (5 : Nat))])]

private def script : Array Json := #[
  response #[call "totals" "warehouse_totals" (Json.mkObj [])] "tool_use",
  response #[call "stock" "low_stock" (Json.mkObj [("warehouse", toJson "north"), ("limit", toJson (10 : Nat))])] "tool_use",
  response #[call "item" "lookup" (Json.mkObj [("sku", toJson "N1")])] "tool_use",
  response #[textBlock "Inventory analysis complete."] "end_turn"]

private def config : Json := Json.mkObj [
  ("model", toJson "scripted-application-contract"), ("maxModelAttempts", toJson (8 : Nat)),
  ("maxToolCalls", toJson (6 : Nat)), ("compactionEnabled", toJson false)]

private def cli (binary : String) (args : Array String) (expected : UInt32 := 0) : IO String := do
  let result ← ProcessIO.capture {
    cmd := binary, args, timeoutMs := 30000, cancelPath := "", stdoutBytes := 1048576,
    stderrBytes := 65536, includeHome := false}
  let stdout := String.fromUTF8! result.stdout
  let stderr := String.fromUTF8! result.stderr
  check s!"CLI {args.toList}: expected exit {expected}, received {result.exitCode}; {stderr}\n{stdout}"
    (result.status == .completed && result.exitCode == some expected)
  check "CLI output unexpectedly truncated" (result.stdoutTotal == result.stdout.size)
  return stdout

private def inspect (binary : String) (session : System.FilePath) : IO (State Inventory.application) := do
  let output ← cli binary #["inspect", session.toString]
  let json ← IO.ofExcept <| Json.parse output
  IO.ofExcept <| json.getObjValAs? (State Inventory.application) "state"

private def resultText (state : State Inventory.application) (id : String) : Except String Json := do
  for message in state.history do
    for block in message.content do
      if (block.getObjValAs? String "tool_use_id").toOption == some id then
        let outer ← Json.parse (← block.getObjValAs? String "content")
        return ← Json.parse (← outer.getObjValAs? String "text")
  throw s!"missing authoritative result for {id}"

private def startArgs (root session : System.FilePath) : Array String := #[
  "run", "--application", "inventory", "--data", (root / "data.json").toString,
  "--config", (root / "config.json").toString, "--script", (root / "script.json").toString,
  "--session", session.toString, "--task", "Which warehouse needs the most replenishment? Inspect its items."]

private def records (session : System.FilePath) : IO (Array Json) :=
  return (← JournalIO.read (session / "journal.jsonl").toString).records

private def run (root : System.FilePath) (binary : String) : IO Unit := do
  jsonFile (root / "data.json") (data 1)
  jsonFile (root / "config.json") config
  jsonFile (root / "script.json") (toJson script)
  let session := root / "continued"
  let _ ← cli binary ((startArgs root session) ++ #["--yield-after", "4"]) 75
  let checkpoint ← inspect binary session
  check "first typed query was not durably completed" (checkpoint.modelAttempts == 1 && checkpoint.toolDispatches == 1)
  let first ← IO.ofExcept <| resultText checkpoint "totals"
  let totals ← IO.ofExcept <| first.getObjValAs? (Array Json) "warehouses"
  check "totals did not reflect actual admitted input"
    (((totals[0]!).getObjValAs? Nat "shortfallUnits").toOption == some 12)
  jsonFile (root / "data.json") (data 10)
  let _ ← cli binary #["resume", session.toString]
  let finished ← inspect binary session
  check "resume did not preserve counts" (finished.modelAttempts == 4 && finished.toolDispatches == 3)
  check "resume changed frozen source data" (finished.config.applicationData == data 1)
  check "inventory unexpectedly acquired workspace authority" finished.config.workspace.isEmpty
  let lookup ← IO.ofExcept <| resultText finished "item"
  let found ← IO.ofExcept <| lookup.getObjVal? "item"
  check "resumed query reread changed input" ((found.getObjValAs? Nat "onHand").toOption == some 1)
  let replayed ← cli binary #["replay", session.toString]
  let replayState ← IO.ofExcept <| (← IO.ofExcept <| Json.parse replayed).getObjVal? "state"
  check "offline replay differs from inspection" (replayState == toJson finished)
  let saved ← records session
  let initial := saved[0]!
  check "application identity not frozen in initial record"
    ((initial.getObjValAs? String "application").toOption == some "inventory")

  -- A new session observes the changed source, while the old session stays frozen.
  let changed := root / "changed"
  let _ ← cli binary (startArgs root changed)
  let changedState ← inspect binary changed
  let changedLookup ← IO.ofExcept <| resultText changedState "item"
  check "new session did not use changed input"
    ((((← IO.ofExcept <| changedLookup.getObjVal? "item").getObjValAs? Nat "onHand").toOption) == some 10)

  -- Simulate losing the reply after a durable query intent. Resume must record
  -- uncertainty and must not dispatch that original query a second time.
  let lost := root / "lost-query"
  let _ ← cli binary ((startArgs root lost) ++ #["--yield-after", "3"]) 75
  let pending ← inspect binary lost
  check "query-intent fixture did not reserve exactly one tool" (pending.toolDispatches == 1)
  match (step pending).1 with
  | .tool _ => pure ()
  | _ => throw <| IO.userError "query-intent fixture not at tool action"
  JournalIO.append (lost / "journal.jsonl").toString <| Json.mkObj [
    ("kind", toJson "intent"), ("id", toJson pending.nextId),
    ("action", actionToJson (step pending).1), ("editWitness", Json.null)]
  let _ ← cli binary #["resume", lost.toString]
  let recovered ← inspect binary lost
  check "lost query refunded its reservation" (recovered.toolDispatches == 3)
  let lostRecords ← records lost
  let atId := lostRecords.filter (fun r => (r.getObjValAs? Nat "id").toOption == some pending.nextId)
  check "lost query was repeated or falsely completed"
    ((atId.filter (fun r => (r.getObjValAs? String "kind").toOption == some "intent")).size == 1 &&
     (atId.filter (fun r => (r.getObjValAs? String "kind").toOption == some "completion")).isEmpty &&
     (atId.filter (fun r => (r.getObjValAs? String "kind").toOption == some "recovery")).size == 1)

  -- Reframed corruption has valid storage checksums, so it exercises application
  -- identity validation rather than merely the journal's checksum detector.
  let unknown := root / "unknown-app"
  JournalIO.createSession unknown.toString
  JournalIO.append (unknown / "journal.jsonl").toString
    (initial.mergeObj (Json.mkObj [("application", toJson "uninstalled")]))
  let before ← IO.FS.readBinFile (unknown / "journal.jsonl")
  let _ ← cli binary #["resume", unknown.toString] 2
  check "unknown application resume advanced the journal"
    ((← IO.FS.readBinFile (unknown / "journal.jsonl")) == before)

  -- Even an otherwise valid first query cannot run when a later call names a
  -- coding capability unavailable to this application.
  let denied := root / "foreign-tool"
  jsonFile (root / "config.json") (config.mergeObj (Json.mkObj [("maxResponseRepairs", toJson (0 : Nat))]))
  jsonFile (root / "script.json") (toJson #[response #[
    call "safe" "warehouse_totals" (Json.mkObj []),
    call "foreign" "create" (Json.mkObj [("path", toJson "unexpected"), ("content", toJson "bad")])]
    "tool_use"])
  let _ ← cli binary (startArgs root denied) 1
  let deniedState ← inspect binary denied
  check "foreign tool batch dispatched an earlier valid call" (deniedState.toolDispatches == 0 && deniedState.seenCallIds.isEmpty)
  IO.println "application CLI: typed queries, frozen data, restart, replay, lost-query recovery, identity and capability boundaries passed"

end Tests.ApplicationRuntime

def main : IO Unit := do
  Harness.Native.installSignals
  let executable ← IO.appPath
  let binary := ((executable.parent.getD ".") / "harness").toString
  let root := System.FilePath.mk s!"/tmp/lean-harness-applications-{← IO.monoNanosNow}"
  IO.FS.createDir root
  try Tests.ApplicationRuntime.run root binary
  finally IO.FS.removeDirAll root
