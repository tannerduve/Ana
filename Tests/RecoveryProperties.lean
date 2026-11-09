import Plausible.Gen
import Harness.Adapter.FilesystemIO
import Harness.Adapter.JournalIO
import Harness.Core.Recovery

/-! Generated linked recovery sequences over real journals and files. Each sequence
keeps one initialized session. Fault choices predict reservations, usage, repair
counts, settled call order and file effects independently of the replayed state.
Pure recovery never invokes the instrumented file adapter. Shrinking recreates the
whole fixture; these are executable tests, not proof tactics or a second runner. -/
namespace Tests.RecoveryProperties
open Lean Harness Plausible

private inductive Fault where
  | completed | beforeEdit | lostEdit | interruptedEdit | uncertainEdit
  | abandonEdit | lostRead | beforeRead | lostModel | malformedModel | lostControl
  deriving Repr, Inhabited, BEq

private def faults : Array Fault := #[.completed, .beforeEdit, .lostEdit, .interruptedEdit,
  .uncertainEdit, .abandonEdit, .lostRead, .beforeRead, .lostModel, .malformedModel, .lostControl]

private def label : Fault → String
  | .completed => "completed" | .beforeEdit => "beforeEdit" | .lostEdit => "lostEdit"
  | .interruptedEdit => "interruptedEdit" | .uncertainEdit => "uncertainEdit"
  | .abandonEdit => "abandonEdit" | .lostRead => "lostRead" | .beforeRead => "beforeRead"
  | .lostModel => "lostModel" | .malformedModel => "malformedModel" | .lostControl => "lostControl"

private structure Expected where
  models : Nat := 0
  tools : Nat := 0
  repairs : Nat := 0
  unknown : Nat := 0
  known : Nat := 0
  edits : Nat := 0
  reads : Nat := 0
  text : String := "initial\n"
  admitted : List String := []
  settled : List (String × Bool) := []

private abbrev Coverage := IO.Ref (Array (String × Nat))

private def hit (coverage : Coverage) (key : String) : IO Unit :=
  coverage.modify fun counts => match counts.findIdx? (·.1 == key) with
    | none => counts.push (key, 1)
    | some index => counts.set! index (key, counts[index]!.2 + 1)

private structure Fixture where
  seed : Nat
  initial : State
  context : ToolContext
  journal : String
  cursor : IO.Ref Recovery.Cursor
  expected : IO.Ref Expected
  edits : IO.Ref Nat
  reads : IO.Ref Nat
  records : IO.Ref (Array Json)
  coverage : Coverage

private def check (seed : Nat) (message : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError s!"recovery sequence seed={seed}: {message}"

private def cursorJson (cursor : Recovery.Cursor) : Json := Json.mkObj [
  ("state", toJson cursor.state), ("pending", toJson cursor.pending),
  ("terminal", toJson cursor.terminal), ("witness", toJson cursor.editWitness),
  ("suspended", toJson cursor.suspended)]

private def settledResults (history : List Harness.Message) : List (String × Bool) := history.flatMap fun message =>
  message.content.toList.filterMap fun block => do
    if (block.getObjValAs? String "type").toOption != some "tool_result" then none else do
      let id ← (block.getObjValAs? String "tool_use_id").toOption
      let isError ← (block.getObjValAs? Bool "is_error").toOption
      pure (id, isError)

private def verify (fixture : Fixture) : IO Unit := do
  let current ← fixture.cursor.get
  let expected ← fixture.expected.get
  check fixture.seed "model reservations differ" (current.state.modelAttempts == expected.models)
  check fixture.seed "tool reservations differ" (current.state.toolDispatches == expected.tools)
  check fixture.seed "repair allowance was restored or miscounted" (current.state.responseRepairs == expected.repairs)
  check fixture.seed "unknown usage differs" (current.state.unknownUsage == expected.unknown)
  check fixture.seed "known usage differs" (current.state.knownInputTokens == 2 * expected.known &&
    current.state.knownOutputTokens == expected.known)
  check fixture.seed "frozen configuration changed" (toJson current.state.config == toJson fixture.initial.config)
  check fixture.seed "admitted call identities differ" (current.state.seenCallIds == expected.admitted)
  check fixture.seed "settled results duplicated, reordered or misclassified" (settledResults current.state.history == expected.settled)
  check fixture.seed "recovery invented an approval grant" current.state.grant.isNone
  check fixture.seed "file bytes differ from independent effect model"
    ((← IO.FS.readFile (fixture.context.workspace ++ "/value.txt")) == expected.text)
  check fixture.seed "edit was lost or repeated" ((← fixture.edits.get) == expected.edits)
  check fixture.seed "read was repeated during recovery" ((← fixture.reads.get) == expected.reads)

private def reopen (fixture : Fixture) : IO Unit := do
  let saved ← JournalIO.read fixture.journal
  check fixture.seed "completed journal prefix differs" (!saved.interrupted && saved.records == (← fixture.records.get))
  let restored ← IO.ofExcept <| Recovery.replay fixture.initial saved.records.toList
  check fixture.seed "replay differs from incremental application"
    (cursorJson restored == cursorJson (← fixture.cursor.get))
  fixture.cursor.set restored
  verify fixture

private def persist (fixture : Fixture) (record : Json) : IO Unit := do
  let next ← IO.ofExcept <| Recovery.applyRecord (← fixture.cursor.get) record
  JournalIO.append fixture.journal record
  fixture.records.modify (·.push record)
  fixture.cursor.set next
  -- Reopen the descriptor and replay the durable prefix at every boundary.
  reopen fixture

private def intent (fixture : Fixture) (witness : Option Recovery.EditWitness := none) : IO Unit := do
  let state := (← fixture.cursor.get).state
  persist fixture <| Json.mkObj [("kind", toJson "intent"), ("id", toJson state.nextId),
    ("action", actionToJson (step state).1), ("editWitness", toJson witness)]

private def completion (fixture : Fixture) (observation : Json) : IO Unit := do
  let state := (← fixture.cursor.get).state
  persist fixture <| Json.mkObj [("kind", toJson "completion"), ("id", toJson state.nextId),
    ("observation", observation)]

private def control (fixture : Fixture) (model tool : Bool := false) : IO Unit := do
  let current ← fixture.cursor.get
  check fixture.seed "expected control boundary" (match (step current.state).1 with | .control => true | _ => false)
  intent fixture
  fixture.expected.modify fun expected => {expected with
    models := expected.models + (if model then 1 else 0), tools := expected.tools + (if tool then 1 else 0)}
  completion fixture (toJson ({} : ControlObservation))

private def recover (fixture : Fixture) (disposition : Recovery.Disposition) : IO Json := do
  let before ← fixture.cursor.get
  let prior ← IO.ofExcept <| Recovery.checkedTarget before
  let expected ← IO.ofExcept <| Recovery.recover before prior.nextId disposition
  let record := Recovery.recoveryRecord prior.nextId disposition
  persist fixture record
  check fixture.seed "recovery record differs from actual recover" (cursorJson (← fixture.cursor.get) == cursorJson expected)
  hit fixture.coverage "recovery"
  return record

private def rejectAgain (fixture : Fixture) (record : Json) : IO Unit := do
  let before ← IO.FS.readBinFile fixture.journal
  check fixture.seed "settled administrative operation accepted twice"
    (match Recovery.applyRecord (← fixture.cursor.get) record with | .error _ => true | _ => false)
  check fixture.seed "rejected record changed durable bytes" ((← IO.FS.readBinFile fixture.journal) == before)
  verify fixture
  hit fixture.coverage "duplicateRejected"

private def resolveEdit (fixture : Fixture) (postimage : String) : IO Json := do
  let before ← fixture.cursor.get
  let prior ← IO.ofExcept <| Recovery.checkedTarget before
  let resolution := Recovery.Resolution.editPostimage postimage
  let expected ← IO.ofExcept <| Recovery.resolve before prior.nextId resolution
  let record := Json.mkObj [("kind", toJson "resolution"), ("id", toJson prior.nextId),
    ("resolution", toJson resolution), ("source", toJson "application_evidence")]
  let forged := record.mergeObj (Json.mkObj [("source", toJson "operator")])
  check fixture.seed "invalid edit resolution provenance accepted"
    (match Recovery.applyRecord before forged with | .error _ => true | _ => false)
  persist fixture record
  check fixture.seed "resolution record differs from actual resolve" (cursorJson (← fixture.cursor.get) == cursorJson expected)
  hit fixture.coverage "resolution"
  return record

private def perform (fixture : Fixture) (call : ToolCall) : IO (ToolObservation ToolResult) := do
  match call.operation with
  | .editFile _ => fixture.edits.modify (· + 1); hit fixture.coverage "effect.edit"
  | .readFile _ => fixture.reads.modify (· + 1); hit fixture.coverage "effect.read"
  | _ => throw <| IO.userError "unexpected fixture effect"
  let result ← FilesystemIO.run fixture.context call
  check fixture.seed "instrumented filesystem operation failed" (match result with | .success _ => true | _ => false)
  return result

private def pendingTail (fixture : Fixture) (ids : List String) : IO Unit := do
  check fixture.seed "administrative settlement changed pending-call order"
    (match (← fixture.cursor.get).state.phase with | .controlTools calls => calls.map (·.id) == ids | _ => false)

private def round (fixture : Fixture) (index : Nat) (fault : Fault) : IO Unit := do
  hit fixture.coverage ("fault." ++ label fault)
  if fault == .lostControl then
    intent fixture
    let _ ← recover fixture .controlLost
    hit fixture.coverage "controlLostNoRefund"
  control fixture (model := true)
  if fault == .lostModel then
    intent fixture
    fixture.expected.modify fun expected => {expected with unknown := expected.unknown + 1}
    let _ ← recover fixture .modelLost
    intent fixture
    completion fixture (toJson WaitObservation.elapsed)
    control fixture (model := true)
    hit fixture.coverage "modelLostFreshAttempt"
  if fault == .malformedModel then
    intent fixture
    fixture.expected.modify fun expected => {expected with unknown := expected.unknown + 1, repairs := expected.repairs + 1}
    completion fixture (toJson (ModelObservation.failure .malformed "generated incomplete response"))
    control fixture (model := true)
    hit fixture.coverage "repairFreshAttempt"
  let old := (← fixture.expected.get).text
  let replacement := s!"value {fixture.seed}/{index}\n"
  let pre ← Native.sha256 old.toUTF8
  let post ← Native.sha256 replacement.toUTF8
  let editArgs : EditArgs := {path := "value.txt", old, new := replacement, expectedSha256 := pre}
  let edit : ToolCall := {id := s!"edit-{index}", operation := .editFile editArgs}
  let read : ToolCall := {id := s!"read-{index}", operation := .readFile {path := "value.txt"}}
  let raw : List RawCall := [
    {id := edit.id, name := "edit", input := toJson editArgs},
    {id := read.id, name := "read", input := Json.mkObj [("path", toJson "value.txt")]}]
  let content := raw.toArray.map fun call => Json.mkObj [
    ("type", toJson "tool_use"), ("id", toJson call.id), ("name", toJson call.name), ("input", call.input)]
  let response : ModelResponse := {
    calls := raw, content, text := "", stop := .toolUse, usage := some {inputTokens := 2, outputTokens := 1}}
  intent fixture
  fixture.expected.modify fun expected => {expected with
    known := expected.known + 1, admitted := expected.admitted ++ [edit.id, read.id]}
  completion fixture (toJson (ModelObservation.success response))
  control fixture (tool := true)
  let witness : Recovery.EditWitness := {path := "value.txt", preimage := pre, postimage := post}
  intent fixture (some witness)
  let editReply ← if fault == .beforeEdit then pure none else do
    let reply ← perform fixture edit
    fixture.expected.modify fun expected => {expected with edits := expected.edits + 1, text := replacement}
    verify fixture
    pure (some reply)
  if fault == .interruptedEdit || fault == .uncertainEdit then
    let reply : ToolObservation ToolResult := if fault == .interruptedEdit then .interrupted "generated interruption"
      else .uncertain "generated lost effect outcome"
    completion fixture (toJson reply)
    let state := (← fixture.cursor.get).state
    match (step state).1 with
    | .finish outcome => persist fixture <| Json.mkObj [("kind", toJson "terminal"),
        ("id", toJson state.nextId), ("outcome", toJson outcome)]
    | _ => throw <| IO.userError "uncertain edit did not stop"
    hit fixture.coverage "terminalRecoveryReopened"
  fixture.expected.modify fun expected => {expected with
    settled := expected.settled ++ [(edit.id, fault == .beforeEdit || fault == .abandonEdit)]}
  if fault == .beforeEdit || fault == .abandonEdit then
    let record ← recover fixture (.mutationAbandoned "generated operator abandonment")
    rejectAgain fixture record
  else if fault == .lostEdit || fault == .interruptedEdit || fault == .uncertainEdit then
    -- The adapter observes and synchronizes the actual postimage before assertion.
    let observed ← FilesystemIO.confirmFileIdentity fixture.context.workspace "value.txt" post
    let record ← resolveEdit fixture observed
    rejectAgain fixture record
  else do
    let some reply := editReply | throw <| IO.userError "missing executed edit reply"
    completion fixture (toJson reply)
  pendingTail fixture [read.id]
  control fixture (tool := true)
  intent fixture
  let readReply ← if fault == .beforeRead then pure none else do
    let reply ← perform fixture read
    fixture.expected.modify fun expected => {expected with reads := expected.reads + 1}
    pure (some reply)
  fixture.expected.modify fun expected => {expected with
    settled := expected.settled ++ [(read.id, fault == .lostRead || fault == .beforeRead)]}
  if fault == .lostRead || fault == .beforeRead then
    let record ← recover fixture .readLost
    rejectAgain fixture record
  else do
    let some reply := readReply | throw <| IO.userError "missing executed read reply"
    completion fixture (toJson reply)
  pendingTail fixture []
  -- Reopening a completed prefix repeatedly cannot launch a file operation.
  reopen fixture
  reopen fixture
  hit fixture.coverage "completedPrefixReplayed"
  control fixture

private def sequence (base : String) (seed : Nat) (choices : Array Fault) (coverage : Coverage) : IO Unit := do
  Native.mkdir base 448
  try
    let workspace := base ++ "/workspace"
    Native.mkdir workspace 448
    IO.FS.writeFile (workspace ++ "/value.txt") "initial\n"
    let config : Config := {
      model := "generated", workspace, commands := .allow,
      compactionEnabled := false, maxContextBytes := 2000000,
      maxModelAttempts := 4 * choices.size + 4, maxToolCalls := 2 * choices.size + 2,
      maxResponseRepairs := choices.size + 1, maxRetries := choices.size + 1}
    let initial := init s!"recovery-{seed}" config "Generated linked file/recovery test"
    let fixture : Fixture := {
      seed, initial,
      context := {workspace, timeoutMs := 30000, outputBytes := 65536, artifactDir := base ++ "/artifacts", cancelPath := base ++ "/cancel"},
      journal := base ++ "/journal", cursor := ← IO.mkRef {state := initial},
      expected := ← IO.mkRef {}, edits := ← IO.mkRef 0, reads := ← IO.mkRef 0,
      records := ← IO.mkRef #[], coverage}
    IO.FS.writeBinFile fixture.journal ByteArray.empty
    for (fault, index) in choices.toList.zipIdx do round fixture index fault
    control fixture (model := true)
    intent fixture
    fixture.expected.modify fun expected => {expected with known := expected.known + 1}
    let finalResponse : ModelResponse := {
      content := #[textBlock "done"], calls := [], text := "done", stop := .endTurn,
      usage := some {inputTokens := 2, outputTokens := 1}}
    completion fixture (toJson (ModelObservation.success finalResponse))
    let state := (← fixture.cursor.get).state
    persist fixture <| Json.mkObj [("kind", toJson "terminal"), ("id", toJson state.nextId),
      ("outcome", toJson (Outcome.final "done"))]
    check seed "terminal session unexpectedly has a recovery target" ((Recovery.target (← fixture.cursor.get)).isNone)
  finally IO.FS.removeDirAll base

private def generate (seed length : Nat) : IO (Array Fault) := do
  let gen : Gen (Array Fault) := do
    let mut result := #[]
    for _ in [:length] do
      let choice ← Gen.choose Nat 0 10 (by decide)
      result := result.push faults[choice.val]!
    pure result
  match (Plausible.runRandWith seed gen).run ⟨length⟩ with
  | .ok result => pure result
  | .error error => throw <| Gen.genFailure error

private def setting (name : String) (fallback limit : Nat) : IO Nat := do
  match ← IO.getEnv name with
  | none => pure fallback
  | some value => match value.toNat? with
    | some n => if 0 < n && n ≤ limit then pure n else throw <| IO.userError s!"{name} outside 1..{limit}"
    | none => throw <| IO.userError s!"{name} is not a natural number"

private def shrink (root : String) (seed : Nat) (choices : Array Fault) : IO (Array Fault) := do
  let mut result := choices
  for attempt in [:min 64 choices.size] do
    let index := attempt % (max 1 result.size)
    let candidate := (result.extract 0 index) ++ (result.extract (index + 1) result.size)
    let failed ← try sequence (root ++ s!"/recovery-shrink-{seed}-{attempt}") seed candidate (← IO.mkRef #[]); pure false
      catch _ => pure true
    if failed then result := candidate
  return result

def run (root : String) : IO Unit := do
  let count ← setting "HARNESS_RECOVERY_SEQUENCES" 40 2000
  let length ← setting "HARNESS_RECOVERY_SEQUENCE_LENGTH" 12 100
  let coverage ← IO.mkRef #[]
  for seed in [71000:71000 + count] do
    let choices ← generate seed length
    try sequence (root ++ s!"/recovery-{seed}") seed choices coverage
    catch error =>
      let reduced ← shrink root seed choices
      throw <| IO.userError s!"{error}\nseed={seed}; deletion-shrunk recovery choices={repr reduced}"
  let counts := (← coverage.get).qsort (fun a b => a.1 < b.1)
  if count ≥ 40 && length ≥ 12 then
    for fault in faults do
      check 0 s!"recovery generator missed {label fault}" (counts.any (·.1 == "fault." ++ label fault))
    for key in ["recovery", "resolution", "duplicateRejected", "terminalRecoveryReopened",
        "modelLostFreshAttempt", "repairFreshAttempt", "controlLostNoRefund", "completedPrefixReplayed"] do
      check 0 s!"recovery generator missed {key}" (counts.any (·.1 == key))
  IO.println s!"Generated recovery: {count} linked sequences × {length} turns passed (seeds71000–{71000 + count - 1}); coverage: {repr counts}"

end Tests.RecoveryProperties
