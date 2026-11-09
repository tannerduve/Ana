import Harness.Core.Transition

/-! Regression for a permission combination unavailable in the original coding instance:
asking for approval cannot repair missing artifact authority or create an approval loop. -/
namespace Tests.ApplicationPolicy
open Harness Lean

private def askingArtifacts : Application :=
  {Coding.application with id := "ask-artifacts", policy := fun _ _ => .ask}

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError s!"generic policy: {label}"

def run : IO Unit := do
  let initial := init "artifact-policy" {model := "scripted"} "read artifact" askingArtifacts
  let call : Call askingArtifacts := {id := "artifact-1", operation := .readArtifact {id := "missing"}}
  let raw : RawCall := {id := call.id, name := "artifact", input := toJson ({id := "missing"} : ArtifactReadArgs)}
  let block := Json.mkObj [("type", toJson "tool_use"), ("id", toJson raw.id),
    ("name", toJson raw.name), ("input", raw.input)]
  let proposed := consumeModel (admitTask initial) (.success {
    content := #[block], calls := [raw], text := "", stop := .toolUse})
  check "artifact query failed batch admission" (proposed.seenCallIds == [call.id])
  for grant in [none, some call] do
    let state := {proposed with grant}
    let admitted := admitTool state call []
    check "missing authority entered another approval request"
      (match admitted.phase with | .controlTools [] => true | _ => false)
    check "denied artifact consumed a tool reservation or retained approval"
      (admitted.toolDispatches == 0 && admitted.grant.isNone)
    let result ← match admitted.history.getLast? with
      | some message => pure message
      | none => throw <| IO.userError "missing denied-call result"
    check "missing artifact did not receive an explicit error result"
      ((result.content[0]!.getObjValAs? Bool "is_error").toOption == some true)
  let normal : Call askingArtifacts := {id := "read-1", operation := .readFile {path := "README.md"}}
  let pending := admitTool initial normal []
  check "valid ask-policy call skipped approval"
    (match pending.phase with | .ask _ _ => true | _ => false)
  let approved := consumeApproval pending normal [] .approved
  let running := admitTool approved normal []
  check "exact approved call was not admitted once"
    (running.toolDispatches == 1 && match running.phase with | .tool _ _ => true | _ => false)
  let coding := init "global-policy" {model := "scripted", commands := .allow, toolPolicy := .deny} "task"
  let command : ToolCall := {id := "command", operation := .runProcess {argv := #["/usr/bin/true"]}}
  check "application-specific allow widened the global deny"
    (!authorized coding.config (some command) command && policy coding.config command == .deny)
  check "global ask widened a domain-specific deny"
    (policy {coding.config with commands := .deny, toolPolicy := .ask} command == .deny)
  IO.println "generic policy: inaccessible artifacts deny without an approval loop; exact approved calls still dispatch"

end Tests.ApplicationPolicy
