import Harness.Adapter.Native

/-! Test-only exercises of the actual foreign-function boundary. Assertions here
are executable checks, not proof axioms. Python supplies independent byte/hash,
metadata and process-result expectations. -/
namespace Tests.NativeABI
open Lean Harness

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def fdCount : IO Nat :=
  Native.withFD (Native.openDir "/proc/self/fd") fun fd =>
    return (← Native.listDir fd 4096).size

private def rejected (action : IO α) : IO Bool := do
  try
    let _ ← action
    return false
  catch _ => return true

private def bytes (j : Json) : IO ByteArray := do
  let values ← IO.ofExcept (j.getObjValAs? (Array Nat) "bytes")
  ensure (values.all (· < 256)) "invalid test bytes"
  return ⟨values.map UInt8.ofNat⟩

private def str (j : Json) (name : String) : IO String :=
  IO.ofExcept (j.getObjValAs? String name)

private def repetitions := 10000

private def byteArrays (j : Json) : IO Json := do
  let path ← str j "path"
  let name ← str j "name"
  let expected ← bytes j
  let digest ← str j "digest"
  let emptyDigest ← str j "emptyDigest"
  let initial ← fdCount
  let names ← Native.withFD (Native.openDir path) fun parent => do
    for _ in [:repetitions] do
      ensure ((← Native.sha256 expected) == digest) "borrowed byte array/hash mismatch"
      ensure ((← Native.sha256 ByteArray.empty) == emptyDigest) "empty byte array/hash mismatch"
      Native.withFD (Native.openReadAt parent name) fun fd => do
        ensure ((← Native.read fd 0).isEmpty) "zero-length native read"
        let actual ← Native.read fd 4096
        ensure (actual == expected) "binary native read mismatch"
        ensure ((← Native.read fd 4096).isEmpty) "EOF native read"
    Native.listDir parent 4096
  let final ← fdCount
  return Json.mkObj [("status", toJson "ok"), ("iterations", toJson repetitions),
    ("fdBefore", toJson initial), ("fdAfter", toJson final), ("names", toJson names),
    ("bytes", toJson (expected.data.map UInt8.toNat)), ("digest", toJson (← Native.sha256 expected))]

private def metadata (j : Json) : IO Json := do
  let path ← str j "path"
  let name ← str j "name"
  let size ← IO.ofExcept (j.getObjValAs? Nat "size")
  let initial ← fdCount
  let result ← Native.withFD (Native.openDir path) fun parent =>
    Native.withFD (Native.openReadAt parent name) fun fd => do
      for _ in [:repetitions] do
        let a ← Native.stat fd
        let b ← Native.statAt parent name
        ensure (a.kind == 1 && b.kind == 1 && a.size == size && b.size == size)
          "boxed Array UInt64 metadata mismatch"
        ensure (a.mode == 416 && b.mode == 416) "metadata mode mismatch"
        let (temporary, output) ← Native.mkTempAt parent 384
        try
          Native.write output ByteArray.empty
          ensure ((← Native.stat output).size == 0) "temporary pair/FD mismatch"
        finally
          Native.close output
          Native.unlinkAt parent temporary
      let absent ← Native.statAt parent "absent"
      let largeRead ← rejected (Native.read fd 4294967297)
      let invalidFd ← rejected (Native.read 4294967295 1)
      let missingOpen ← rejected (Native.openReadAt parent "absent")
      let nulPath ← rejected (Native.openReadAt parent (name ++ "\x00suffix"))
      return Json.mkObj [("kind", toJson (← Native.stat fd).kind), ("size", toJson (← Native.stat fd).size),
        ("mode", toJson (← Native.stat fd).mode.toNat), ("missingKind", toJson absent.kind),
        ("largeReadRejected", toJson largeRead), ("invalidFdRejected", toJson invalidFd),
        ("missingOpenRejected", toJson missingOpen), ("nulPathRejected", toJson nulPath)]
  return result.mergeObj <| Json.mkObj [("status", toJson "ok"), ("iterations", toJson repetitions),
    ("fdBefore", toJson initial), ("fdAfter", toJson (← fdCount))]

private def waitExited (pid : UInt32) : IO UInt32 := do
  for _ in [:2000] do
    if let some code ← Native.peekExit pid then return code
    IO.sleep 1
  throw <| IO.userError "ABI test process did not exit"

private def process (j : Json) : IO Json := do
  let path ← str j "path"
  let payload ← bytes j
  let initial ← fdCount
  let child ← Native.spawn "/bin/sh" #["-c", "cat; printf '%s' \"$ABI_VALUE\"; exit 255"]
    (some path) #[("PATH", some "/usr/bin:/bin"), ("ABI_VALUE", some "λ🙂"), ("ABI_ABSENT", none)]
  let mut inputOpen := true
  let mut stdoutOpen := true
  let mut stderrOpen := true
  let mut maySignal := true
  let mut reaped := false
  try
    for _ in [:repetitions] do
      ensure ((← Native.readAvailable child.stdoutFd 4096).isNone) "would-block must be none"
      ensure ((← Native.peekExit child.pid).isNone) "running process must have no exit status"
    let written ← Native.writeAvailable child.inputFd payload 0
    ensure (written.toNat == payload.size) "boxed UInt64 write count mismatch"
    ensure ((← Native.writeAvailable child.inputFd payload written) == 0) "end-offset write mismatch"
    inputOpen := false
    Native.close child.inputFd
    let mut output := ByteArray.empty
    let mut eof := false
    for _ in [:2000] do
      if eof then break
      let _ ← Native.pollReadable child.stdoutFd 10
      if let some chunk ← Native.readAvailable child.stdoutFd 4096 then
        if chunk.isEmpty then eof := true else output := output ++ chunk
    ensure eof "EOF must be some empty, not none"
    let code ← waitExited child.pid
    -- Keep the leader unreaped through the last possible group signal. Never
    -- signal this numeric group again after attempting a potentially reaping wait.
    maySignal := false
    let waited ← Native.tryWait child.pid
    ensure (waited == some code) "boxed Option UInt32 exit status mismatch"
    reaped := true
    stdoutOpen := false
    Native.close child.stdoutFd
    stderrOpen := false
    Native.close child.stderrFd
    return Json.mkObj [("status", toJson "ok"), ("iterations", toJson repetitions),
      ("output", toJson (output.data.map UInt8.toNat)), ("exitCode", toJson code.toNat),
      ("written", toJson written.toNat), ("fdBefore", toJson initial), ("fdAfter", toJson (← fdCount))]
  finally
    if inputOpen then try Native.close child.inputFd catch _ => pure ()
    if !reaped then
      if maySignal then try Native.signalGroup child.pid 9 catch _ => pure ()
      try
        let _ ← waitExited child.pid
        let _ ← Native.tryWait child.pid
      catch _ => pure ()
    if stdoutOpen then try Native.close child.stdoutFd catch _ => pure ()
    if stderrOpen then try Native.close child.stderrFd catch _ => pure ()

def run (j : Json) : IO Json := do
  match ← str j "case" with
  | "bytes" => byteArrays j
  | "metadata" => metadata j
  | "process" => process j
  | _ => throw <| IO.userError "unknown native ABI test case"

end Tests.NativeABI
