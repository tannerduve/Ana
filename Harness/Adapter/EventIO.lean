import Harness.Adapter.Native

/-! Bounded terminal/event buffering. Pipe/TTY backpressure cannot stall the
agent loop. Regular-file writes still rely on filesystem responsiveness, as do
journal writes. Undelivered output changes the CLI exit status; the durable
journal remains the authoritative record. -/
namespace Harness.EventIO

private structure Pending where
  bytes : ByteArray := ByteArray.empty
  offset : Nat := 0
  dropped : Nat := 0
  failed : Bool := false

structure Sink where
  fd : Option Native.FD
  private pending : IO.Ref Pending

structure Output where
  stdout : Sink
  stderr : Sink

private def capacity : Nat := 128 * 1024

private def openSink (fd : UInt32) : IO Sink := do
  let descriptor ← try pure (some (← Native.openOutput fd)) catch _ => pure none
  return {fd := descriptor, pending := ← IO.mkRef {}}

def create : IO Output := do
  let stdout ← openSink 1
  let stderr ← openSink 2
  if let (some outFd, some errFd) := (stdout.fd, stderr.fd) then
    let shared ← try
      let outInfo ← Native.stat outFd
      let errInfo ← Native.stat errFd
      pure (outInfo.kind == 1 && errInfo.kind == 1 &&
        outInfo.device == errInfo.device && outInfo.inode == errInfo.inode)
      catch _ => pure false
    if shared then
      Native.close errFd
      return {stdout, stderr := stdout}
  return {stdout, stderr}

private def drain (sink : Sink) : IO Unit := do
  let some fd := sink.fd | return
  let p ← sink.pending.get
  if p.failed || p.offset ≥ p.bytes.size then return
  try
    let written ← Native.writeAvailable fd p.bytes p.offset.toUInt64
    let offset := p.offset + written.toNat
    sink.pending.set <| if offset ≥ p.bytes.size then {p with bytes := ByteArray.empty, offset := 0}
      else {p with offset}
  catch _ => sink.pending.set {bytes := ByteArray.empty, dropped := p.dropped + 1, failed := true}

/-- Each supplied string is one indivisible queued record. A partial OS write
retains its remainder; overflow drops a later whole record, never its prefix. -/
private def writeBytes (sink : Sink) (bytes : ByteArray) : IO Unit := do
  drain sink
  let p ← sink.pending.get
  if sink.fd.isNone || p.failed || p.bytes.size - p.offset + bytes.size > capacity then
    sink.pending.set {p with dropped := p.dropped + 1}
  else
    sink.pending.set {p with bytes := p.bytes.extract p.offset p.bytes.size ++ bytes, offset := 0}
    drain sink

def write (sink : Sink) (text : String) : IO Unit := writeBytes sink text.toUTF8

def line (sink : Sink) (text : String) : IO Unit := write sink (text ++ "\n")

def terminalText (text : String) : String := String.ofList <| text.toList.map fun c =>
  if c == '\n' || c == '\t' || (c.toNat ≥ 32 && !(127 ≤ c.toNat && c.toNat ≤ 159)) then c else '�'

def human (sink : Sink) (text : String) : IO Unit := write sink (terminalText text)
def humanLine (sink : Sink) (text : String) : IO Unit := human sink (text ++ "\n")

private def hex4 (value : Nat) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList [digits[value / 4096 % 16]!, digits[value / 256 % 16]!,
    digits[value / 16 % 16]!, digits[value % 16]!]

/-- Exact approval metadata is printable ASCII JSON. C1, bidi, zero-width and
other non-ASCII characters cannot alter its terminal presentation. Escapes remain
JSON-decodable, including surrogate pairs for characters above U+FFFF. -/
def approvalJSON (value : Lean.Json) : String := Id.run do
  let mut escaped := ""
  for character in value.pretty.toList do
    let code := character.toNat
    if code < 127 then escaped := escaped.push character
    else if code ≤ 65535 then escaped := escaped ++ "\\u" ++ hex4 code
    else
      let scalar := code - 65536
      escaped := escaped ++ "\\u" ++ hex4 (55296 + scalar / 1024) ++
        "\\u" ++ hex4 (56320 + scalar % 1024)
  return escaped

def dropped (output : Output) : IO Nat := do
  if output.stdout.fd == output.stderr.fd then return (← output.stdout.pending.get).dropped
  return (← output.stdout.pending.get).dropped + (← output.stderr.pending.get).dropped

private def empty (sink : Sink) : IO Bool := do
  let p ← sink.pending.get
  return p.offset ≥ p.bytes.size

private def flush (output : Output) : Nat → IO Unit
  | 0 => pure ()
  | remaining + 1 => do
    drain output.stdout
    drain output.stderr
    if (← empty output.stdout) && (← empty output.stderr) then return
    IO.sleep 5
    flush output remaining

def flushPending (output : Output) : IO Bool := do
  flush output 20
  return (← empty output.stdout) && (← empty output.stderr)

/-- Large offline inspection/final text is streamed in bounded chunks. Each chunk
has a bounded flush allowance; a stalled consumer ends delivery explicitly. -/
def document (output : Output) (text : String) : IO Unit := do
  let bytes := (text ++ "\n").toUTF8
  let started ← IO.monoMsNow
  for index in [: (bytes.size + 32767) / 32768] do
    if (← IO.monoMsNow) - started > 5000 || !(← flushPending output) then
      output.stdout.pending.modify fun p => {p with dropped := p.dropped + 1}
      return
    writeBytes output.stdout (bytes.extract (index * 32768) ((index + 1) * 32768))
    if (← output.stdout.pending.get).dropped > 0 then return

/-- At most 100 ms cooperative flushing. False means output was lost or remains
undelivered; it does not change a previously persisted task outcome. -/
def finish (output : Output) : IO Bool := do
  flush output 20
  return (← dropped output) == 0 && (← empty output.stdout) && (← empty output.stderr)

def close (output : Output) : IO Unit := do
  if let some fd := output.stdout.fd then
    try Native.close fd catch _ => pure ()
  if output.stderr.fd != output.stdout.fd then
    if let some fd := output.stderr.fd then
      try Native.close fd catch _ => pure ()

end Harness.EventIO
