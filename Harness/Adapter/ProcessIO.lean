import Harness.Adapter.RuntimeTypes
import Harness.Adapter.Native
import Harness.Adapter.FilesystemIO
import Harness.Adapter.Sandbox

/-!
One-process supervision. The Lean core owns permission, admission, and retry policy.
The native spawn primitive reports exec errors before returning. Pipes are drained
without retaining unbounded output; subprocesses run in a new
process group, with a deadline and cancellation checked throughout their lifetime.
-/
namespace Harness.ProcessIO

inductive CaptureStatus where
  | completed | failedToStart | interrupted | uncertain | timedOut
  deriving Repr, BEq

inductive StopCause where
  | cancelled | localDeadline | invocationDeadline
  deriving Repr, BEq

structure CaptureRequest where
  cmd : String
  args : Array String := #[]
  cwd : Option System.FilePath := none
  input : ByteArray := ByteArray.empty
  timeoutMs : Nat
  /-- Preserve the caller's operation clock across request preparation. -/
  startedMs : Option Nat := none
  invocationDeadlineMs : Option Nat := none
  localDeadline : Bool := false
  cancelPath : String
  stdoutBytes : Nat
  stderrBytes : Nat := 4096
  includeHome : Bool := true
  /-- Trusted adapter overrides only; never supplied by a model tool argument. -/
  environment : Option (Array (String × Option String)) := none
  /-- Borrowed setup FDs, remapped to 3 + index. The target must not inherit them. -/
  inherited : Array Native.FD := #[]
  /-- Bounded, nonblocking work only. Exceptions trigger supervised cleanup. -/
  onStdout : ByteArray → IO Unit := fun _ => pure ()
  /-- Optional shared retention bound across stdout and stderr. -/
  combinedBytes : Option Nat := none
  mergedBytes : Nat := 0
  /-- Short grace for a sandbox's init to settle after its monitored target exits. -/
  settleGraceMs : Nat := 0

structure CaptureResult where
  status : CaptureStatus
  exitCode : Option UInt32 := none
  stdout : ByteArray := ByteArray.empty
  stderr : ByteArray := ByteArray.empty
  stdoutTotal : Nat := 0
  stderrTotal : Nat := 0
  message : String := ""
  merged : ByteArray := ByteArray.empty
  totalMerged : Nat := 0
  stopCause : Option StopCause := none

private abbrev Running := Native.Spawned

private structure CaptureState where
  stdout : ByteArray := ByteArray.empty
  stderr : ByteArray := ByteArray.empty
  stdoutTotal : Nat := 0
  stderrTotal : Nat := 0
  merged : ByteArray := ByteArray.empty
  totalMerged : Nat := 0

/-- Signal cancellation and the durable session cancellation file are both observed. -/
def cancelled (path : String) : IO Bool := do
  if ← Native.isCancelled then return true
  return !path.isEmpty && (← (System.FilePath.mk path).pathExists)

private def invocationExpired (deadline : Option Nat) (now : Nat) : Bool :=
  deadline.any (now ≥ ·)

private def sanitizedEnv (includeHome : Bool) : IO (Array (String × Option String)) := do
  let keys := if includeHome then #["HOME", "PATH", "LANG", "LC_ALL", "TMPDIR"]
    else #["PATH", "LANG", "LC_ALL", "TMPDIR"]
  let mut result := #[]
  for key in keys do
    if let some value ← IO.getEnv key then result := result.push (key, some value)
  return result

private def closeQuietly (fd : Native.FD) : IO Unit := do
  try Native.close fd catch _ => pure ()

private def signalQuietly (pid signal : UInt32) : IO Unit := do
  try Native.signalGroup pid signal catch _ => pure ()

private def waitForReap (pid : UInt32) : Nat → IO Bool
  | 0 => do
    try return (← Native.tryWait pid).isSome catch _ => return false
  | n+1 => do
    try
      if (← Native.tryWait pid).isSome then return true
    catch _ => return false
    IO.sleep 10
    waitForReap pid n

private def appendBounded (kept chunk : ByteArray) (cap : Nat) : ByteArray :=
  kept ++ chunk.extract 0 (cap - kept.size)

private def collect (request : CaptureRequest) (state : IO.Ref CaptureState)
    (isStdout : Bool) (chunk : ByteArray) : IO Unit := do
  let previous ← state.get
  let labeled := (if isStdout then "[stdout] " else "[stderr] ").toUTF8 ++ chunk
  let remaining := request.combinedBytes.map (fun cap => cap - previous.stdout.size - previous.stderr.size)
  let stdoutCap := min request.stdoutBytes (remaining.map (· + previous.stdout.size) |>.getD request.stdoutBytes)
  let stderrCap := min request.stderrBytes (remaining.map (· + previous.stderr.size) |>.getD request.stderrBytes)
  let saved := if isStdout then
      {previous with stdout := appendBounded previous.stdout chunk stdoutCap, stdoutTotal := previous.stdoutTotal + chunk.size}
    else {previous with stderr := appendBounded previous.stderr chunk stderrCap, stderrTotal := previous.stderrTotal + chunk.size}
  let saved := {saved with merged := appendBounded saved.merged labeled request.mergedBytes, totalMerged := saved.totalMerged + labeled.size}
  state.set saved

private def drain (request : CaptureRequest) (state : IO.Ref CaptureState)
    (fd : Native.FD) (isStdout eof : Bool) : IO Bool := do
  if eof then return true
  match ← Native.readAvailable fd 65536 with
  | none => return false
  | some bytes =>
    if bytes.isEmpty then return true
    collect request state isStdout bytes
    if isStdout then request.onStdout bytes
    return false

private structure Progress where
  inputOffset : Nat := 0
  stdoutEOF : Bool := false
  stderrEOF : Bool := false
  exitCode : Option UInt32 := none
  exitedAt : Option Nat := none
  stoppingAt : Option Nat := none
  forced : Bool := false
  uncertain : Bool := false
  residualGroup : Bool := false
  reason : String := ""
  stopCause : Option StopCause := none

private def makeResult (state : IO.Ref CaptureState) (status : CaptureStatus)
    (exitCode : Option UInt32) (message : String) (stopCause : Option StopCause := none) : IO CaptureResult := do
  let s ← state.get
  return { status, exitCode, message, stopCause, stdout := s.stdout, stderr := s.stderr, stdoutTotal := s.stdoutTotal, stderrTotal := s.stderrTotal, merged := s.merged, totalMerged := s.totalMerged }

private partial def supervise (request : CaptureRequest) (running : Running)
    (started : Nat) (state : IO.Ref CaptureState) (inputOwner : IO.Ref (Option Native.FD))
    (maySignal : IO.Ref Bool) (progress : Progress) : IO CaptureResult := do
  let isCancelled ← cancelled request.cancelPath
  let now ← IO.monoMsNow
  let mut p := progress
  let globalExpired := invocationExpired request.invocationDeadlineMs now
  if isCancelled then
    p := {p with stopCause := some .cancelled}
  else if globalExpired && p.stopCause != some .cancelled then
    p := {p with stopCause := some .invocationDeadline}
  if p.stoppingAt.isNone && (isCancelled || globalExpired || now - started ≥ request.timeoutMs) then
    let cause := if isCancelled then StopCause.cancelled else if globalExpired then .invocationDeadline
      else if request.localDeadline then .localDeadline else .invocationDeadline
    let reason := match cause with
      | .cancelled => "cancelled"
      | .localDeadline => "operation deadline exceeded"
      | .invocationDeadline => "invocation deadline exceeded"
    p := {p with stoppingAt := some now, stopCause := some cause, reason}
    signalQuietly running.pid 15
  if let some fd ← inputOwner.get then
    if p.stoppingAt.isSome || p.inputOffset ≥ request.input.size then
      inputOwner.set none
      closeQuietly fd
    else
      let count ← Native.writeAvailable fd request.input p.inputOffset.toUInt64
      p := {p with inputOffset := p.inputOffset + count.toNat}
  p := {p with stdoutEOF := ← drain request state running.stdoutFd true p.stdoutEOF}
  p := {p with stderrEOF := ← drain request state running.stderrFd false p.stderrEOF}
  if p.exitCode.isNone then
    -- Keep the exited leader unreaped while group cleanup can still signal its PGID.
    -- This reserves its identity against reuse by an unrelated process group.
    if let some code ← Native.peekExit running.pid then
      p := {p with exitCode := some code, exitedAt := some now}
  if p.exitCode.isSome then
    let residual ← Native.groupHasOthers running.pid
    p := {p with residualGroup := residual}
    if residual && p.stoppingAt.isNone && now - p.exitedAt.getD now ≥ request.settleGraceMs then
      p := {p with stoppingAt := some now, uncertain := true, reason := "background process group required cleanup; descendant completion unknown"}
      signalQuietly running.pid 15
    if p.stdoutEOF && p.stderrEOF && !residual then
      if let some fd ← inputOwner.get then
        inputOwner.set none
        closeQuietly fd
      -- /proc membership observation is not atomic. End the pinned group before
      -- releasing its identity, including members that raced the observation.
      signalQuietly running.pid 9
      -- No path, including the outer error handler, may signal after reaping.
      maySignal.set false
      if (← Native.tryWait running.pid).isNone then
        return ← makeResult state .uncertain p.exitCode "exited process could not be reaped"
      let status := if p.uncertain then .uncertain else if p.stoppingAt.isSome then .interrupted else .completed
      return ← makeResult state status p.exitCode p.reason p.stopCause
    if p.stoppingAt.isNone && now - p.exitedAt.getD now ≥ 250 then
      p := {p with stoppingAt := some now, uncertain := true, reason := "output pipes remained open after process exit; descendant outcome unknown"}
      signalQuietly running.pid 15
  if let some stoppedAt := p.stoppingAt then
    if !p.forced && now - stoppedAt ≥ 250 then
      signalQuietly running.pid 9
      p := {p with forced := true}
    if now - stoppedAt ≥ 2000 then
      if let some fd ← inputOwner.get then
        inputOwner.set none
        closeQuietly fd
      maySignal.set false
      signalQuietly running.pid 9
      let _ ← waitForReap running.pid 10
      return ← makeResult state .uncertain p.exitCode
        s!"cleanup deadline exceeded; descendants or output pipes may remain (stdout EOF: {p.stdoutEOF}, stderr EOF: {p.stderrEOF}, residual group: {p.residualGroup})"
  IO.sleep 10
  supervise request running started state inputOwner maySignal p

/-- Run one command with bounded separate raw stdout/stderr. Input is passed only
through a pipe and is never written to an artifact or diagnostic. -/
def capture (request : CaptureRequest) : IO CaptureResult := do
  if ← cancelled request.cancelPath then
    return {status := .interrupted, message := "cancelled before process launch"}
  if request.timeoutMs == 0 then
    return {status := .interrupted, message := "deadline expired before process launch"}
  if request.cmd.isEmpty || request.cmd.toList.contains '\x00' || request.args.size > 1024 ||
      request.args.any (fun arg => arg.toList.contains '\x00') then
    return {status := .failedToStart, message := "invalid process arguments"}
  if request.stdoutBytes > 32 * 1024 * 1024 || request.stderrBytes > 16 * 1024 * 1024 ||
      request.mergedBytes > 1024 * 1024 || request.input.size > 32 * 1024 * 1024 || request.settleGraceMs > 1000 then
    return {status := .failedToStart, message := "process buffer limit exceeds supported bound"}
  let started := request.startedMs.getD (← IO.monoMsNow)
  let state ← IO.mkRef ({} : CaptureState)
  if ← cancelled request.cancelPath then
    return {status := .interrupted, message := "cancelled before process launch"}
  let env ← match request.environment with
    | some values => pure values
    | none => sanitizedEnv request.includeHome
  let isCancelled ← cancelled request.cancelPath
  let now ← IO.monoMsNow
  if isCancelled || now - started ≥ request.timeoutMs ||
      invocationExpired request.invocationDeadlineMs now then
    return {status := .interrupted, message := "cancelled or deadline expired before process launch"}
  let running ← try
      Native.spawn request.cmd request.args (request.cwd.map System.FilePath.toString) env request.inherited
    catch e => return {status := .failedToStart, message := s!"launcher failure: {e}"}
  let inputOwner ← IO.mkRef (some running.inputFd)
  let maySignal ← IO.mkRef true
  try
    let result ← try
        supervise request running started state inputOwner maySignal {}
      catch error =>
        if let some fd ← inputOwner.get then
          inputOwner.set none
          closeQuietly fd
        if ← maySignal.get then
          maySignal.set false
          signalQuietly running.pid 9
          let _ ← waitForReap running.pid 200
        makeResult state .uncertain none s!"adapter failure after process launch: {(toString error).take 512}; effects unknown"
    return result
  finally
    if let some fd ← inputOwner.get then closeQuietly fd
    closeQuietly running.stdoutFd
    closeQuietly running.stderrFd

private def displayText (bytes : ByteArray) (limit : Nat) : String :=
  let rec loop : Nat → Nat → Nat → String → String
    | 0, _, _, text => text
    | fuel+1, offset, remaining, text =>
      if offset ≥ bytes.size then text
      else match bytes.utf8DecodeChar? offset with
        | some c => if c.utf8Size > remaining then text
          else loop fuel (offset + c.utf8Size) (remaining - c.utf8Size) (text.push c)
        | none => if remaining < 3 then text
          else loop fuel (offset + 1) (remaining - 3) (text.push '�')
  loop bytes.size 0 limit ""

private def readStatus (fd : Native.FD) : Nat → ByteArray → IO ByteArray
  | 0, _ => throw <| IO.userError "sandbox status exceeded framing bound"
  | fuel + 1, bytes => do
    let chunk ← Native.readAvailable fd (8193 - bytes.size).toUInt64
    match chunk with
    | none => throw <| IO.userError "sandbox status channel remains open after cleanup"
    | some chunk =>
      if chunk.isEmpty then return bytes
      let bytes := bytes ++ chunk
      if bytes.size > 8192 then throw <| IO.userError "sandbox status exceeded byte limit"
      readStatus fd fuel bytes

/-- Only the trusted wrapper owns this pipe. A child-pid receipt establishes
namespace-init creation, never target exec or completion. -/
private def sandboxStatus (bytes : ByteArray) : Except String (Nat × Option UInt32) := do
  let some text := String.fromUTF8? bytes | throw "sandbox status is not UTF-8"
  unless text.endsWith "\n" do throw "sandbox status lacks final framing"
  let mut child : Option Nat := none
  let mut code : Option UInt32 := none
  for line in text.splitOn "\n" do
    unless line.isEmpty do
      let value ← Lean.Json.parse line
      let _ ← value.getObj?
      if (value.getObjVal? "child-pid").isOk then
        let pid ← value.getObjValAs? Nat "child-pid"
        if child.isSome || code.isSome || pid == 0 || pid > 4294967295 ||
            (value.getObjVal? "exit-code").isOk then throw "invalid sandbox child status order"
        child := some pid
      else if (value.getObjVal? "exit-code").isOk then
        let status ← value.getObjValAs? Nat "exit-code"
        if child.isNone || code.isSome || status > 255 then throw "invalid sandbox exit status"
        code := some status.toUInt32
      else throw "unrecognized sandbox status record"
  let some pid := child | throw "sandbox namespace init was not established"
  return (pid, code)

/-- The group scanner must see PIDs in the caller's namespace. Merely reading
an ancestor's proc mount can silently compare unrelated PID/PGID numbers.
Complete visibility of owned processes remains a supported-host requirement. -/
private def validateProcView : IO Unit := do
  let pid := toString (← Native.getPid)
  Native.withFD (Native.openDir "/proc") fun proc => do
    unless (← Native.readLinkAt proc "self") == pid do
      throw <| IO.userError "procfs PID view does not match the caller"
    Native.withFD (Native.openDirAt proc pid) fun current =>
      Native.withFD (Native.openReadAt current "status") fun fd => do
        let bytes ← Native.read fd 65537
        if bytes.size > 65536 || !(← Native.read fd 1).isEmpty then
          throw <| IO.userError "procfs status exceeds supported bound"
        let some text := String.fromUTF8? bytes | throw <| IO.userError "procfs status is not UTF-8"
        let lines := (text.splitOn "\n").filter (·.startsWith "NSpid:")
        unless lines == ["NSpid:\t" ++ pid] do
          throw <| IO.userError "procfs PID namespace does not match the caller"

private def captureSandbox (context : ToolContext) (args : ProcessArgs)
    (request : CaptureRequest) : IO CaptureResult := do
  validateProcView
  let (reader, writer) ← Native.statusPipe
  let writerOpen ← IO.mkRef true
  try
    let outcome ← Sandbox.withPlan context args writer fun plan => do
      let result ← capture {request with
        cmd := "/usr/bin/bwrap", args := plan.args, cwd := none,
        environment := some #[], inherited := plan.inherited, settleGraceMs := 100}
      writerOpen.set false
      Native.close writer
      let localTimeout := result.status == .interrupted && result.stopCause == some .localDeadline
      if result.status != .completed && !localTimeout then return result
      try
        let (_, exitCode) ← IO.ofExcept <| sandboxStatus (← readStatus reader 16 ByteArray.empty)
        if localTimeout then
          if ← cancelled context.cancelPath then
            return {result with stopCause := some .cancelled, message := "cancelled during process cleanup"}
          if invocationExpired context.invocationDeadlineMs (← IO.monoMsNow) then
            return {result with stopCause := some .invocationDeadline, message := "invocation deadline expired during process cleanup"}
          -- Under the fixed profile, init existed before monitor exit and stays
          -- in its host PGID throughout setup and teardown. The complete group
          -- scan therefore observed init dead/absent, after Linux finished
          -- terminating its namespace. The final SIGKILL alone is not evidence.
          return {result with
            status := .timedOut
            exitCode := none
            message := "operation deadline exceeded; owned sandbox attempt stopped; target exit and partial effects are not established"}
        let some code := exitCode | throw <| IO.userError "sandbox target completion was not established"
        unless result.exitCode == some code do
          throw <| IO.userError "sandbox wrapper and target statuses differ"
        return {result with exitCode := some code}
      catch error =>
        return {result with status := .uncertain, message := s!"{error}; wrapper exit was {result.exitCode}"}
    return outcome
  finally
    if ← writerOpen.get then closeQuietly writer
    closeQuietly reader

/-- Check the frozen profile before paid inference. The full workspace scan is
repeated on resume; dispatch revalidates roots under the single-writer contract. -/
def validateSandbox (workspace session : String) (profile : ExecutionProfile)
    (toolchainRoots : Array String) (timeoutMs : Nat := 5000) : IO Unit := do
  if profile == .host then return
  let started ← IO.monoMsNow
  validateProcView
  let _ ← Sandbox.mountSources workspace session toolchainRoots
  Sandbox.validateWorkspace workspace (timeoutMs - ((← IO.monoMsNow) - started))
  let context : ToolContext := {
    workspace, timeoutMs, outputBytes := 4096,
    artifactDir := session ++ "/artifacts", cancelPath := session ++ "/cancel",
    executionProfile := profile, toolchainRoots}
  let result ← captureSandbox context {argv := #["/usr/bin/true"]} {
    cmd := "/usr/bin/bwrap", timeoutMs, startedMs := some started,
    cancelPath := context.cancelPath, stdoutBytes := 4096, stderrBytes := 4096}
  unless result.status == .completed && result.exitCode == some 0 do
    throw <| IO.userError ("bubblewrap profile unavailable; no host fallback: " ++
      result.message ++ " " ++ displayText result.stderr 4096)

/-- Carry out one already-authorized process tool inside a validated working directory.
The process group is supervised, but working-directory confinement is not a sandbox. -/
def run (context : ToolContext) (args : ProcessArgs) : IO (ToolObservation ToolResult) := do
  if context.executionProfile == .host && (context.workspaceReadOnly || !context.resourceMounts.isEmpty) then
    return .failure "scoped application processes require bubblewrap; host execution cannot enforce their mounts"
  let operationStarted ← IO.monoMsNow
  if ← cancelled context.cancelPath then return .interrupted "cancelled before process launch"
  if args.argv.isEmpty then return .failure "process argv must not be empty"
  let started ← IO.mkRef false
  try
    let available ← ArtifactIO.availableBytes context
    FilesystemIO.withWorkspaceDir context.workspace args.cwd fun dir => do
      let pid ← Native.getPid
      started.set true
      let request : CaptureRequest := {
        cmd := args.argv[0]!, args := args.argv.extract 1 args.argv.size,
        cwd := some s!"/proc/{pid}/fd/{dir}", timeoutMs := context.timeoutMs,
        startedMs := some operationStarted, invocationDeadlineMs := context.invocationDeadlineMs,
        localDeadline := context.localDeadline,
        cancelPath := context.cancelPath, stdoutBytes := min available context.maxArtifactBytes,
        stderrBytes := min available context.maxArtifactBytes, combinedBytes := some available,
        mergedBytes := context.outputBytes }
      let result ← if context.executionProfile == .bubblewrap then captureSandbox context args request
        else capture request
      let mut text := displayText result.merged context.outputBytes
      if result.totalMerged > context.outputBytes then
        text := text ++ s!"\n[output truncated: {result.totalMerged} bytes produced]"
      if !result.message.isEmpty then text := text ++ s!"\n[{result.message}]"
      let mut value : ToolResult := {text, exitCode := result.exitCode.map (fun n => Int.ofNat n.toNat)}
      if result.totalMerged > context.outputBytes || result.status == .interrupted || result.status == .uncertain || result.status == .timedOut then
        try
          if result.stdoutTotal > 0 then
            let ref ← ArtifactIO.store context "stdout" result.stdout result.stdoutTotal
            value := {value with artifacts := value.artifacts.push ref}
          if result.stderrTotal > 0 then
            let ref ← ArtifactIO.store context "stderr" result.stderr result.stderrTotal
            value := {value with artifacts := value.artifacts.push ref}
        catch _ => return .uncertain "output artifact persistence failed after process launch; effects may have occurred" (some value)
      for ref in value.artifacts do
        value := {value with text := value.text ++ s!"\n[artifact {ref.id}: {ref.label}, {ref.storedBytes}/{ref.totalBytes} bytes retained]"}
      match result.status with
      | .completed => return .success value
      | .failedToStart => return .failure text
      | .interrupted => return .interrupted (text ++ "\n[operation may have changed files]") (some value)
      | .uncertain => return .uncertain text (some value)
      | .timedOut =>
        if ← cancelled context.cancelPath then
          return .interrupted "cancelled while retaining timeout output; effects may be partial" (some value)
        if invocationExpired context.invocationDeadlineMs (← IO.monoMsNow) then
          return .interrupted "invocation deadline expired while retaining timeout output; effects may be partial" (some value)
        return .timedOut (some {value with exitCode := none, sha256 := none})
  catch e =>
    if ← started.get then return .uncertain s!"process adapter failed after admission; effects unknown: {e}"
    else return .failure s!"process preflight failed: {e}"

end Harness.ProcessIO
