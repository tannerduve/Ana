import Harness.Runner
import Harness.Applications.CodingIO
import Harness.Applications.InventoryIO

/-! Statically installed application selection. New sessions freeze the chosen
application and validated configuration; resume selects only the saved identity.
No journal can name an executable, dynamic plugin or arbitrary interpreter. -/

open Lean Harness

private def usage : String := "harness run [--application coding|inventory] --config CONFIG --task TEXT [--workspace PATH] [--data FILE] [--restrict-capabilities FILE] [--session PATH] [--json] [--script FILE] [--yield-after N]\nharness resume SESSION [--json] [--yield-after N]\nharness continue SESSION --task TEXT [--json] [--yield-after N]\nharness inspect SESSION\nharness replay SESSION\nharness cancel SESSION\nharness resolve SESSION --operation ID --status completed|abandoned --note TEXT [--resources-settled] [--exit-code N] [--json]\nharness policy check PARENT CHILD\nharness policy restrict PARENT LIMIT\nCoding requires --workspace. Inventory freezes --data as starting stock; reservations change only that session's inventory.\nPolicies are lists of allow-rule lists; LIMIT and --restrict-capabilities take one allow-rule list. A restriction adds a ceiling and cannot grant new authority. Process rules authorize an exact launch, not its downstream filesystem effects."

private def value (args : List String) (key : String) : Option String :=
  match args with
  | "--json" :: tail => value tail key
  | "--resources-settled" :: tail => value tail key
  | a :: b :: tail => if a == key then some b else value tail key
  | _ => none

private def hasEvents : List String → Bool
  | [] => false
  | "--json" :: _ => true
  | "--resources-settled" :: tail => hasEvents tail
  | _ :: _ :: tail => hasEvents tail
  | _ => false

private def required (args : List String) (key : String) : IO String :=
  match value args key with
  | some v => pure v
  | none => throw <| IO.userError s!"missing {key}"

private def parseOptions (args : List String) : Except String Unit := loop args []
where
  loop : List String → List String → Except String Unit
    | [], _ => .ok ()
    | "--json" :: tail, seen =>
      if seen.contains "--json" then .error "duplicate option: --json"
      else loop tail ("--json" :: seen)
    | flag :: _value :: tail, seen =>
      if seen.contains flag then .error s!"duplicate option: {flag}"
      else if ["--application", "--data", "--workspace", "--config", "--task", "--session",
          "--script", "--yield-after", "--restrict-capabilities"].contains flag then
        loop tail (flag :: seen)
      else .error s!"unknown option: {flag}"
    | [flag], _ => .error s!"missing value or unknown option: {flag}"

private def parseResolutionOptions : List String → Except String Unit
  | [] => .ok ()
  | "--json" :: tail | "--resources-settled" :: tail => parseResolutionOptions tail
  | flag :: _value :: tail =>
    if ["--operation", "--status", "--note", "--exit-code"].contains flag
    then parseResolutionOptions tail else .error s!"unknown resolution option: {flag}"
  | [flag] => .error s!"missing value or unknown resolution option: {flag}"

private def resourcesSettled : List String → Bool
  | "--resources-settled" :: _ => true
  | "--json" :: tail => resourcesSettled tail
  | _ :: _ :: tail => resourcesSettled tail
  | _ => false

private def readJson (path : String) : IO Json := do
  IO.ofExcept <| Json.parse (← IO.FS.readFile path)

/-- Trusted startup data/policy only. The validated value is frozen in the session;
resume never reopens this path. Reject links/special files and bound reads and parsing. -/
private def readBoundedJson (label path : String) : IO Json := do
  let path := System.FilePath.mk path
  let some name := path.fileName | throw <| IO.userError s!"{label} path has no filename"
  Native.withFD (Native.openDir (path.parent.getD ".").toString) fun parent =>
    Native.withFD (Native.openReadAt parent name) fun fd => do
      let info ← Native.stat fd
      unless info.kind == 1 && info.links == 1 && info.size ≤ 1024 * 1024 do
        throw <| IO.userError s!"{label} must be a regular, singly-linked file of at most 1 MiB"
      let mut bytes := ByteArray.empty
      for _ in [:18] do
        let chunk ← Native.read fd 65536
        if chunk.isEmpty then
          let some text := String.fromUTF8? bytes | throw <| IO.userError s!"{label} is not UTF-8"
          return ← IO.ofExcept <| JsonBounds.parse text
        bytes := bytes ++ chunk
        if bytes.size > 1024 * 1024 then throw <| IO.userError s!"{label} exceeds 1 MiB"
      throw <| IO.userError s!"{label} read limit exceeded"

private def readPolicy (path : String) : IO Capability.Policy := do
  let policy : Capability.Policy ← IO.ofExcept <| fromJson? (← readBoundedJson "capability policy" path)
  IO.ofExcept (Capability.validate policy)
  return policy

private def readCapabilityLimit (path : String) : IO (List Capability.Access) := do
  let limit : List Capability.Access ← IO.ofExcept <| fromJson? (← readBoundedJson "capability restriction" path)
  IO.ofExcept (Capability.validate [limit])
  return limit

private def installed (name : String)
    (body : (app : Application) → ApplicationIO.Runtime app → IO α) : IO α :=
  match name with
  | "coding" => body Coding.application CodingIO.runtime
  | "inventory" => body Inventory.application InventoryIO.runtime
  | _ => throw <| IO.userError s!"unknown installed application: {name}"

private def yieldAfter (options : List String) : IO Nat :=
  match value options "--yield-after" with
  | none => pure 0
  | some value => match value.toNat? with
    | some count => pure count
    | none => throw <| IO.userError "--yield-after must be a natural number"

private def absolute (p : String) : IO String := do
  if (System.FilePath.mk p).isAbsolute then return p
  return ((← IO.currentDir) / p).toString

private def defaultSession (identity : String) : IO String := do
  let root ← match ← IO.getEnv "XDG_STATE_HOME" with
    | some path =>
      if (System.FilePath.mk path).isAbsolute then pure (System.FilePath.mk path)
      else homeState
    | none => homeState
  return (root / "lean-harness" / "sessions" / identity).toString
where
  homeState : IO System.FilePath := do
    let some homePath ← IO.getEnv "HOME"
      | throw <| IO.userError "HOME or absolute XDG_STATE_HOME is required; alternatively provide --session"
    unless (System.FilePath.mk homePath).isAbsolute do
      throw <| IO.userError "HOME must be absolute; alternatively provide --session"
    return System.FilePath.mk homePath / ".local" / "state"

private def runCLI (output : EventIO.Output) (args : List String) : IO UInt32 := do
  match args with
  | [] | ["--help"] | ["help"] => EventIO.document output usage; return 0
  | ["policy", "check", parentFile, childFile] =>
    let parent ← readPolicy parentFile
    let child ← readPolicy childFile
    let contained := Capability.checkContained child parent
    EventIO.document output <| (Json.mkObj [
      ("status", toJson (if contained then "contained" else "not_established"))]).compress
    return if contained then 0 else 3
  | ["policy", "restrict", parentFile, limitFile] =>
    let parent ← readPolicy parentFile
    let limit ← readCapabilityLimit limitFile
    let restricted := Capability.restrict parent limit
    IO.ofExcept (Capability.validate restricted)
    EventIO.document output (toJson restricted).compress
    return 0
  | "policy" :: _ => throw <| IO.userError usage
  | "run" :: options =>
    IO.ofExcept (parseOptions options)
    installed ((value options "--application").getD "coding") fun app runtime => do
      let workspace ← if app.id == "coding" then required options "--workspace" else do
        if (value options "--workspace").isSome then
          throw <| IO.userError "inventory has no workspace authority"
        pure ""
      let raw ← readJson (← required options "--config")
      let fields ← IO.ofExcept raw.getObj?
      let model ← IO.ofExcept (raw.getObjValAs? String "model")
      let defaults : Config := {model, workspace, instructions := app.defaultInstructions}
      let known ← IO.ofExcept (toJson defaults).getObj?
      for (key, _) in fields.toList do
        unless known.contains key do throw <| IO.userError s!"unknown configuration field: {key}"
      let config : Config ← IO.ofExcept <| fromJson? ((toJson defaults).mergeObj raw)
      if app.id == "inventory" && !config.workspace.isEmpty then
        throw <| IO.userError "inventory has no workspace authority"
      let config := {config with workspace}
      let config ← match value options "--data" with
        | none => pure config
        | some path => do
          unless app.id == "inventory" do throw <| IO.userError "--data requires the inventory application"
          if fields.contains "applicationData" then
            throw <| IO.userError "supply either --data or applicationData, not both"
          pure {config with applicationData := ← readBoundedJson "dataset" path}
      let config ← match value options "--restrict-capabilities" with
        | none => pure config
        | some path => do
          let limit ← readCapabilityLimit path
          let policy := Capability.restrict config.capabilityPolicy limit
          IO.ofExcept (Capability.validate policy)
          pure {config with capabilityPolicy := policy}
      if config.model.isEmpty || config.operationTimeoutMs == 0 || config.maxElapsedMs == 0 then
        throw <| IO.userError "model and positive operation/session time limits are required"
      if config.maxArtifactBytes > 16 * 1024 * 1024 || config.maxSessionArtifactBytes > 256 * 1024 * 1024 then
        throw <| IO.userError "artifact limits exceed supported bounds (16 MiB each, 256 MiB per session)"
      if config.toolchainRoots.size > 8 then throw <| IO.userError "at most eight toolchain roots are supported"
      if config.executionProfile == .host && !config.toolchainRoots.isEmpty then
        throw <| IO.userError "toolchainRoots requires the bubblewrap execution profile"
      let task ← required options "--task"
      let id ← IO.monoNanosNow
      let session ← match value options "--session" with
        | some path => absolute path
        | none => defaultSession s!"{id}"
      let script ← match value options "--script" with
        | none => pure none
        | some path => do
          let raw ← readJson path
          pure (some (← IO.ofExcept raw.getArr?))
      Runner.start runtime {session, output, script, events := hasEvents options, yieldAfter := ← yieldAfter options} config task
  | "resolve" :: session :: options =>
    IO.ofExcept (parseResolutionOptions options)
    let some operation := (← required options "--operation").toNat?
      | throw <| IO.userError "operation must be a natural-number ID from inspect"
    let note ← required options "--note"
    let resolution ← match ← required options "--status" with
      | "completed" => do
        let some code := (← required options "--exit-code").toInt?
          | throw <| IO.userError "exit code must be an integer in 0..255"
        pure (Recovery.Resolution.processCompleted code note)
      | "abandoned" =>
        if (value options "--exit-code").isSome then
          throw <| IO.userError "abandoned outcomes cannot supply an exit code"
        else pure (Recovery.Resolution.processAbandoned note)
      | _ => throw <| IO.userError "resolution status must be completed or abandoned"
    let o : Runner.Options := {session := ← absolute session, output, events := hasEvents options}
    let (application, version) ← Runner.savedApplication o
    unless application == Coding.application.id && version == Coding.application.version do
      throw <| IO.userError "this application has no process resolution interface"
    let abandonNote := if (value options "--status") == some "abandoned" then some note else none
    Runner.resolveOperation CodingIO.runtime o operation resolution (resourcesSettled options) abandonNote
  | cmd :: session :: options =>
    IO.ofExcept (parseOptions options)
    let session ← absolute session
    let o : Runner.Options := {session, output, events := hasEvents options, yieldAfter := ← yieldAfter options}
    match cmd with
    | "inspect" | "replay" | "resume" | "continue" | "cancel" =>
      if (value options "--data").isSome || (value options "--config").isSome ||
          (value options "--workspace").isSome || (value options "--script").isSome ||
          (value options "--restrict-capabilities").isSome then
        throw <| IO.userError "saved application configuration cannot be overridden"
      let (application, version) ← Runner.savedApplication o
      if let some requested := value options "--application" then
        unless requested == application do throw <| IO.userError "application differs from saved session"
      installed application fun app runtime => do
        unless version == app.version do throw <| IO.userError "unsupported application version"
        if cmd == "continue" then Runner.continueSession runtime o (← required options "--task")
        else
          if (value options "--task").isSome then
            throw <| IO.userError "use continue SESSION --task TEXT to add a follow-up"
          if cmd == "resume" then Runner.resume runtime o
          else if cmd == "cancel" then Runner.cancel app o else Runner.inspect app o
    | _ => throw <| IO.userError usage
  | _ => throw <| IO.userError usage

def main (args : List String) : IO UInt32 := do
  let output ← EventIO.create
  try
    let code ← try
      Native.installSignals
      runCLI output args
    catch e =>
      EventIO.humanLine output.stderr s!"harness: {e}"
      pure 2
    let delivered ← EventIO.finish output
    return if code == 0 && !delivered then 74 else code
  finally EventIO.close output
