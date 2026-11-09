import Harness.Adapter.RuntimeTypes
import Harness.Adapter.Native
import Harness.Adapter.FilesystemIO

/-!
One-process supervision. The Lean core owns permission, admission, and retry policy.
The native spawn primitive reports exec errors before returning. Pipes are drained
without retaining unbounded output; subprocesses run in a new
process group, with a deadline and cancellation checked throughout their lifetime.
-/
namespace Harness.ProcessIO

inductive CaptureStatus where
  | completed | failedToStart | interrupted | uncertain
  deriving Repr, BEq

structure CaptureRequest where
  cmd : String
  args : Array String := #[]
  cwd : Option System.FilePath := none
  input : ByteArray := ByteArray.empty
  timeoutMs : Nat
  cancelPath : String
  stdoutBytes : Nat
  stderrBytes : Nat := 4096
  includeHome : Bool := true
  artifactDir : Option String := none
  mergedBytes : Nat := 0

structure CaptureResult where
  status : CaptureStatus
  exitCode : Option UInt32 := none
  stdout : ByteArray := ByteArray.empty
  stderr : ByteArray := ByteArray.empty
  stdoutTotal : Nat := 0
  stderrTotal : Nat := 0
  message : String := ""
  artifact : Option String := none
  merged : ByteArray := ByteArray.empty
  totalMerged : Nat := 0

private abbrev Running := Native.Spawned

private structure CaptureState where
  stdout : ByteArray := ByteArray.empty
  stderr : ByteArray := ByteArray.empty
  stdoutTotal : Nat := 0
  stderrTotal : Nat := 0
  merged : ByteArray := ByteArray.empty
  totalMerged : Nat := 0
  retained : Nat := 0

private def artifactLimit : Nat := 16 * 1024 * 1024

/-- Signal cancellation and the durable session cancellation file are both observed. -/
def cancelled (path : String) : IO Bool := do
  if ← Native.isCancelled then return true
  return !path.isEmpty && (← (System.FilePath.mk path).pathExists)

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
    (artifactFd : Option Native.FD) (isStdout : Bool) (chunk : ByteArray) : IO Unit := do
  let previous ← state.get
  let labeled := (if isStdout then "[stdout] " else "[stderr] ").toUTF8 ++ chunk
  let saved := if isStdout then
      {previous with stdout := appendBounded previous.stdout chunk request.stdoutBytes, stdoutTotal := previous.stdoutTotal + chunk.size}
    else {previous with stderr := appendBounded previous.stderr chunk request.stderrBytes, stderrTotal := previous.stderrTotal + chunk.size}
  let saved := {saved with merged := appendBounded saved.merged labeled request.mergedBytes, totalMerged := saved.totalMerged + labeled.size}
  state.set saved
  if let some fd := artifactFd then
    let part := labeled.extract 0 (artifactLimit - saved.retained)
    unless part.isEmpty do
      Native.write fd part
      state.modify fun s => {s with retained := s.retained + part.size}

private def drain (request : CaptureRequest) (state : IO.Ref CaptureState)
    (artifactFd : Option Native.FD) (fd : Native.FD) (isStdout eof : Bool) : IO Bool := do
  if eof then return true
  match ← Native.readAvailable fd 65536 with
  | none => return false
  | some bytes =>
    if bytes.isEmpty then return true
    collect request state artifactFd isStdout bytes
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
  reason : String := ""

private def makeResult (state : IO.Ref CaptureState) (status : CaptureStatus)
    (exitCode : Option UInt32) (message : String) (artifact : Option String) : IO CaptureResult := do
  let s ← state.get
  return { status, exitCode, message, artifact, stdout := s.stdout, stderr := s.stderr, stdoutTotal := s.stdoutTotal, stderrTotal := s.stderrTotal, merged := s.merged, totalMerged := s.totalMerged }

private partial def supervise (request : CaptureRequest) (running : Running)
    (started : Nat) (state : IO.Ref CaptureState) (artifactFd : Option Native.FD)
    (artifact : Option String) (inputOwner : IO.Ref (Option Native.FD))
    (maySignal : IO.Ref Bool) (progress : Progress) : IO CaptureResult := do
  let now ← IO.monoMsNow
  let mut p := progress
  if p.stoppingAt.isNone && ((← cancelled request.cancelPath) || now - started ≥ request.timeoutMs) then
    p := {p with stoppingAt := some now, reason := "cancelled or deadline exceeded"}
    signalQuietly running.pid 15
  if let some fd ← inputOwner.get then
    if p.stoppingAt.isSome || p.inputOffset ≥ request.input.size then
      inputOwner.set none
      closeQuietly fd
    else
      let count ← Native.writeAvailable fd request.input p.inputOffset.toUInt64
      p := {p with inputOffset := p.inputOffset + count.toNat}
  p := {p with stdoutEOF := ← drain request state artifactFd running.stdoutFd true p.stdoutEOF}
  p := {p with stderrEOF := ← drain request state artifactFd running.stderrFd false p.stderrEOF}
  if p.exitCode.isNone then
    -- Keep the exited leader unreaped while group cleanup can still signal its PGID.
    -- This reserves its identity against reuse by an unrelated process group.
    if let some code ← Native.peekExit running.pid then
      p := {p with exitCode := some code, exitedAt := some now}
  if p.exitCode.isSome then
    let residual ← Native.groupHasOthers running.pid
    if residual && p.stoppingAt.isNone then
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
        return ← makeResult state .uncertain p.exitCode "exited process could not be reaped" artifact
      let status := if p.uncertain then .uncertain else if p.stoppingAt.isSome then .interrupted else .completed
      return ← makeResult state status p.exitCode p.reason artifact
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
        "cleanup deadline exceeded; descendants or output pipes may remain" artifact
  IO.sleep 10
  supervise request running started state artifactFd artifact inputOwner maySignal p

private def createArtifact (directory : String) : IO (String × Native.FD) := do
  IO.FS.createDirAll directory
  let dir ← Native.openDir directory
  try
    let pid ← Native.getPid
    let now ← IO.monoNanosNow
    let name := s!"output-{pid}-{now}.log"
    let fd ← Native.openWriteAt dir name true false 384
    try Native.sync dir
    catch e =>
      closeQuietly fd
      throw e
    return (directory ++ "/" ++ name, fd)
  finally Native.close dir

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
  if request.stdoutBytes > 32 * 1024 * 1024 || request.stderrBytes > 1024 * 1024 ||
      request.mergedBytes > 1024 * 1024 || request.input.size > 32 * 1024 * 1024 then
    return {status := .failedToStart, message := "process buffer limit exceeds supported bound"}
  let started ← IO.monoMsNow
  let state ← IO.mkRef ({} : CaptureState)
  let artifact ← try
      match request.artifactDir with
      | none => pure none
      | some directory => pure (some (← createArtifact directory))
    catch _ => return {status := .failedToStart, message := "cannot create process output artifact"}
  try
    if ← cancelled request.cancelPath then
      return {status := .interrupted, message := "cancelled before process launch"}
    let env ← sanitizedEnv request.includeHome
    if (← cancelled request.cancelPath) || (← IO.monoMsNow) - started ≥ request.timeoutMs then
      return {status := .interrupted, message := "cancelled or deadline expired before process launch"}
    let running ← try
        Native.spawn request.cmd request.args (request.cwd.map System.FilePath.toString) env
      catch e => return {status := .failedToStart, message := s!"launcher failure: {e}"}

    let inputOwner ← IO.mkRef (some running.inputFd)
    let maySignal ← IO.mkRef true
    let outcome ← try
      let result ← try
          supervise request running started state (artifact.map Prod.snd) (artifact.map Prod.fst) inputOwner maySignal {}
        catch _ =>
          if let some fd ← inputOwner.get then
            inputOwner.set none
            closeQuietly fd
          if ← maySignal.get then
            maySignal.set false
            signalQuietly running.pid 9
            let _ ← waitForReap running.pid 200
          makeResult state .uncertain none "adapter failure after process launch; effects unknown" (artifact.map Prod.fst)
      if let some (_, fd) := artifact then
        try Native.sync fd
        catch _ => return {result with status := .uncertain, message := "output artifact synchronization failed after process launch; effects unknown"}
      pure result
    finally
      if let some fd ← inputOwner.get then closeQuietly fd
      closeQuietly running.stdoutFd
      closeQuietly running.stderrFd
    return outcome

  finally
    if let some (_, fd) := artifact then closeQuietly fd

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

/-- Carry out one already-authorized process tool inside a validated working directory.
The process group is supervised, but working-directory confinement is not a sandbox. -/
def run (context : ToolContext) (args : ProcessArgs) : IO (ToolObservation ToolResult) := do
  if ← cancelled context.cancelPath then return .interrupted "cancelled before process launch"
  if args.argv.isEmpty then return .failure "process argv must not be empty"
  let started ← IO.mkRef false
  try
    FilesystemIO.withWorkspaceDir context.workspace args.cwd fun dir => do
      let pid ← Native.getPid
      started.set true
      let result ← capture {
        cmd := args.argv[0]!, args := args.argv.extract 1 args.argv.size, cwd := some s!"/proc/{pid}/fd/{dir}", timeoutMs := context.timeoutMs, cancelPath := context.cancelPath, stdoutBytes := 0, stderrBytes := 0, artifactDir := some context.artifactDir, mergedBytes := context.outputBytes }
      let mut text := displayText result.merged context.outputBytes
      if result.totalMerged > context.outputBytes then
        text := text ++ s!"\n[output truncated: {result.totalMerged} bytes produced]"
        if let some artifact := result.artifact then text := text ++ s!"\n[artifact: {artifact}]"
      if result.totalMerged > artifactLimit then
        text := text ++ s!"\n[artifact contains only first {artifactLimit} bytes]"
      if !result.message.isEmpty then text := text ++ s!"\n[{result.message}]"
      let value : ToolResult := {text, exitCode := result.exitCode.map (fun n => Int.ofNat n.toNat), artifact := if result.totalMerged > context.outputBytes then result.artifact else none}
      match result.status with
      | .completed => return .success value
      | .failedToStart => return .failure text
      | .interrupted => return .interrupted (text ++ "\n[operation may have changed files]")
      | .uncertain => return .uncertain text
  catch e =>
    if ← started.get then return .uncertain s!"process adapter failed after admission; effects unknown: {e}"
    else return .failure s!"process preflight failed: {e}"

end Harness.ProcessIO
