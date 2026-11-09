import Harness.Adapter.ProcessIO

namespace Harness.ApprovalIO

private def readAnswer (fd : Native.FD) (cancelPath : String) (started timeoutMs : Nat) :
    Nat → ByteArray → IO ApprovalObservation
  | 0, _ => return .interrupted
  | polls+1, answer => do
    if (← ProcessIO.cancelled cancelPath) || (← IO.monoMsNow) - started ≥ timeoutMs then
      return .interrupted
    if ← Native.pollReadable fd 25 then
      match ← Native.readAvailable fd (128 - answer.size).toUInt64 with
      | none => readAnswer fd cancelPath started timeoutMs polls answer
      | some bytes =>
        if bytes.isEmpty then return .denied
        let answer := answer ++ bytes
        let line := answer.data.toList.takeWhile (· != 10)
        if line.length < answer.size then
          if (← ProcessIO.cancelled cancelPath) || (← IO.monoMsNow) - started ≥ timeoutMs then
            return .interrupted
          return if line == [121, 101, 115] then .approved else .denied
        if answer.size ≥ 128 then return .denied
        readAnswer fd cancelPath started timeoutMs polls answer
    else readAnswer fd cancelPath started timeoutMs polls answer

/-- Observe one exact human answer on the controlling terminal; the pure core
binds that answer to the displayed operation. No terminal means denial. -/
def ask (timeoutMs : Nat) (cancelPath : String) : IO ApprovalObservation := do
  if ← ProcessIO.cancelled cancelPath then return .interrupted
  if timeoutMs == 0 then return .interrupted
  let fd ← try Native.openTTY catch _ => return .denied
  try
    let started ← IO.monoMsNow
    readAnswer fd cancelPath started timeoutMs (timeoutMs + 128) ByteArray.empty
  catch _ => return .denied
  finally Native.close fd

end Harness.ApprovalIO
