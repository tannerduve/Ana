import Tests.Core
import Harness.Core.Recovery

namespace Tests.Turns
open Harness Lean Tests.Core

private structure Recorded where
  cursor : Recovery.Cursor
  records : List Json := []

private def observe (run : Recorded) (observation : Json) : Except String Recorded := do
  let state := run.cursor.state
  let intent := Json.mkObj [("kind", toJson "intent"), ("id", toJson state.nextId),
    ("action", actionToJson (step state).1)]
  let waiting ← Recovery.applyRecord run.cursor intent
  let completion := Json.mkObj [("kind", toJson "completion"), ("id", toJson state.nextId),
    ("observation", observation)]
  let next ← Recovery.applyRecord waiting completion
  return {cursor := next, records := run.records ++ [intent, completion]}

private def finish (run : Recorded) : Except String Recorded := do
  match (step run.cursor.state).1 with
  | .finish outcome =>
    let record := Json.mkObj [("kind", toJson "terminal"), ("id", toJson run.cursor.state.nextId),
      ("outcome", toJson outcome)]
    return {cursor := ← Recovery.applyRecord run.cursor record, records := run.records ++ [record]}
  | _ => throw "fixture did not reach a terminal action"

private def continueWith (run : Recorded) (task : String) : Except String Recorded := do
  let s := run.cursor.state
  let record := Recovery.userTurnRecord s.nextId (s.turn + 1) task
  return {cursor := ← Recovery.applyRecord run.cursor record, records := run.records ++ [record]}

private def resultRows (s : State) : List (String × String × Bool) :=
  s.history.flatMap fun message => message.content.toList.filterMap fun block => do
    if (block.getObjValAs? String "type").toOption != some "tool_result" then none else do
      return (← (block.getObjValAs? String "tool_use_id").toOption,
        ← (block.getObjValAs? String "content").toOption,
        ← (block.getObjValAs? Bool "is_error").toOption)

def run : IO Unit := do
  let config : Config := {cfg with maxResponseRepairs := 0}
  let initial := init "turn-session" config "first task"
  let first : Recorded := {cursor := {state := initial}}
  let ready ← IO.ofExcept <| observe first (toJson ({} : ControlObservation))
  let done ← IO.ofExcept <| observe ready (toJson finalResponse)
  expect ((Recovery.newTurn done.cursor done.cursor.state.nextId 1 "too early").isError)
    "a completion without durable terminal admitted a new turn"
  let terminal ← IO.ofExcept <| finish done
  let next ← IO.ofExcept <| continueWith terminal "second task"
  let before := terminal.cursor.state
  let after := next.cursor.state
  expect (after.turn == 1 && after.nextId == before.nextId + 1 &&
    after.modelAttempts == before.modelAttempts && after.toolDispatches == before.toolDispatches &&
    after.unknownUsage == before.unknownUsage && toJson after.config == toJson before.config &&
    toJson (after.history.take before.history.length) == toJson before.history && after.grant.isNone)
    "new turn changed authority, history prefix, or cumulative accounting"
  let duplicate := Recovery.userTurnRecord before.nextId 1 "second task"
  expect ((Recovery.applyRecord next.cursor duplicate).isError) "duplicate user turn accepted"
  expect ((Recovery.newTurn terminal.cursor before.nextId 2 "wrong index").isError)
    "incorrect turn index accepted"
  expect ((continueWith terminal "  ").isError) "empty follow-up accepted"
  let second ← IO.ofExcept <| observe next (toJson ({} : ControlObservation))
  let second ← IO.ofExcept <| observe second (toJson finalResponse)
  let second ← IO.ofExcept <| finish second
  let replayed ← IO.ofExcept <| Recovery.replay initial second.records
  expect (toJson replayed.state == toJson second.cursor.state && replayed.terminal &&
    replayed.state.modelAttempts == 2 && replayed.state.turn == 1)
    "multi-turn replay lost a turn or refunded an attempt"

  let raw2 := {readCall with id := "read-2"}
  let batch : ModelObservation := .success {
    content := #[callBlock readCall, callBlock raw2],
    calls := [readCall, raw2], text := "", stop := .toolUse}
  let queued ← IO.ofExcept <| observe ready (toJson batch)
  let cancelled ← IO.ofExcept <| observe queued (toJson ({cancelled := true} : ControlObservation))
  let cancelled ← IO.ofExcept <| finish cancelled
  expect (resultRows cancelled.cursor.state ==
    [(readCall.id, cancelledCallText, true), (raw2.id, cancelledCallText, true)] &&
    cancelled.cursor.state.toolDispatches == 0 && historyValid cancelled.cursor.state.history)
    "control cancellation failed to settle the undispatched batch exactly in order"
  let continued ← IO.ofExcept <| continueWith cancelled "inspect after cancellation"
  expect (continued.cursor.state.seenCallIds == [readCall.id,raw2.id] &&
    continued.cursor.state.turn == 1 && continued.cursor.state.toolDispatches == 0)
    "cancelled follow-up reused IDs or counted skipped calls as dispatches"
  let continued ← IO.ofExcept <| observe continued (toJson ({} : ControlObservation))
  let rejected ← IO.ofExcept <| observe continued (toJson (toolResponse readCall))
  expect (isFailure rejected.cursor.state && rejected.cursor.state.toolDispatches == 0)
    "a later turn reused a previously admitted call identity"

  let dispatched ← IO.ofExcept <| observe queued (toJson ({} : ControlObservation))
  let completed ← IO.ofExcept <| observe dispatched
    (toJson (ToolObservation.success ({text := "observed"} : ToolResult)))
  let cancelledTail ← IO.ofExcept <| observe completed (toJson ({cancelled := true} : ControlObservation))
  expect ((resultRows cancelledTail.cursor.state).map (fun row => (row.1,row.2.2)) ==
    [(readCall.id,false),(raw2.id,true)] && cancelledTail.cursor.state.toolDispatches == 1)
    "cancellation changed a completed result or dispatched its suffix"
  let uncertain ← IO.ofExcept <| observe dispatched
    (toJson (ToolObservation.uncertain "unknown effects" (none : Option ToolResult)))
  let uncertain ← IO.ofExcept <| finish uncertain
  expect ((continueWith uncertain "must not bypass recovery").isError)
    "new turn bypassed an unresolved effect"
  -- Recovery legitimately refers to the old operation ID. It must not make that
  -- identity available to a fresh intent, even after another turn is admitted.
  let recovery := Recovery.recoveryRecord dispatched.cursor.state.nextId .readLost
  let recovered : Recorded := {
    cursor := ← IO.ofExcept (Recovery.applyRecord uncertain.cursor recovery),
    records := uncertain.records ++ [recovery]}
  let recovered ← IO.ofExcept <| observe recovered (toJson ({cancelled := true} : ControlObservation))
  let recovered ← IO.ofExcept <| finish recovered
  let later ← IO.ofExcept <| continueWith recovered "new work after explicit recovery"
  let staleIntent := Json.mkObj [("kind", toJson "intent"),
    ("id", toJson dispatched.cursor.state.nextId),
    ("action", actionToJson (step later.cursor.state).1)]
  expect ((Recovery.applyRecord later.cursor staleIntent).isError)
    "recovery and a new turn made an old intent identity reusable"
  let replayed ← IO.ofExcept <| Recovery.replay initial later.records
  expect (toJson replayed.state == toJson later.cursor.state &&
    replayed.state.toolDispatches == 1 && replayed.state.turn == 1)
    "mixed recovery/turn replay changed dispatch accounting or state"

  let askInitial := init "ask-session" {config with toolPolicy := .ask} "approval cancellation"
  let askReady ← IO.ofExcept <| observe {cursor := {state := askInitial}} (toJson ({} : ControlObservation))
  let askQueued ← IO.ofExcept <| observe askReady (toJson batch)
  let asking ← IO.ofExcept <| observe askQueued (toJson ({} : ControlObservation))
  let denied ← IO.ofExcept <| observe asking (toJson ApprovalObservation.interrupted)
  let denied ← IO.ofExcept <| finish denied
  expect (resultRows denied.cursor.state ==
    [(readCall.id,cancelledCallText,true),(raw2.id,cancelledCallText,true)])
    "interrupted approval failed to settle its entire undispatched queue"
  let _ ← IO.ofExcept <| continueWith denied "continue without an old grant"
  let exhausted := {terminal.cursor with state := {before with modelAttempts := before.config.maxModelAttempts}}
  expect ((Recovery.newTurn exhausted before.nextId 1 "no budget reset").isError)
    "new turn silently replenished an exhausted session"

end Tests.Turns
