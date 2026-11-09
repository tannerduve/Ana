import Harness.Adapter.Provider
import Harness.Adapter.SSE
import Harness.Adapter.ProcessIO

/-!
One HTTP attempt, supervised by the Lean process adapter. Curl supplies HTTPS
transport only; request construction and response normalization remain in Lean.
Credentials and payload are passed in a bounded stdin configuration, never argv
or a temporary file. Curl's startup configuration and proxy use are disabled.
-/
namespace Harness.ProviderIO
open Lean

def anthropicEndpoint : String := "https://api.anthropic.com/v1/messages"

structure Options where
  timeoutMs : Nat := 60000
  /-- Absolute caller deadline, retained across encoding and curl preparation. -/
  invocationDeadlineMs : Option Nat := none
  responseBytes : Nat := 2000000
  cancelPath : String := ""
  /-- Override only for credential-free HTTP tests on numeric loopback addresses. -/
  endpoint : String := anthropicEndpoint
  deriving Repr

/-- A complete HTTP body is distinct from an interrupted or uncertain attempt. -/
inductive HttpObservation where
  | complete (status : Nat) (body : String)
  | failure (kind : FailureClass) (message : String)
  | interrupted
  | uncertain (message : String)
  deriving Repr, ToJson, FromJson

-- Leave four bytes for curl's status footer within ProcessIO's capture bound.
private def maximumBytes : Nat := 32 * 1024 * 1024 - 4

private def validPort (port : String) : Bool :=
  !port.isEmpty && port.toList.all Char.isDigit &&
    (port.toNat?).any (fun value => 0 < value && value ≤ 65535)

/-- No DNS name, userinfo, alternate IP spelling, or URL glob can select a host.
Numeric loopback test endpoints never receive the environment's API credential. -/
def isLoopbackEndpoint (endpoint : String) : Bool :=
  if !endpoint.startsWith "http://" ||
      !endpoint.toList.all (fun c => 33 ≤ c.toNat && c.toNat ≤ 126 && c != '\\' && c != '#') then
    false
  else
    let authority := ((endpoint.drop 7).toString.splitOn "/").head!
    authority == "127.0.0.1" || authority == "[::1]" ||
      (authority.startsWith "127.0.0.1:" && validPort (authority.drop 10).toString) ||
      (authority.startsWith "[::1]:" && validPort (authority.drop 6).toString)

private def quoted (value : String) : String :=
  let escaped := (((value.replace "\\" "\\\\").replace "\"" "\\\"").replace "\n" "\\n").replace "\r" "\\r"
  "\"" ++ escaped.replace "\t" "\\t" ++ "\""

private def configValue (name value : String) : String :=
  name ++ " = " ++ quoted value ++ "\n"

private def seconds (milliseconds : Nat) : String :=
  let fraction := toString (milliseconds % 1000)
  toString (milliseconds / 1000) ++ "." ++
    String.ofList (List.replicate (3 - fraction.length) '0') ++ fraction

private def curlConfig (payload : String) (options : Options) (key : Option String) : String :=
  "silent\nno-buffer\ngloboff\nhttp1.1\nno-location\ndisallow-username-in-url\n" ++
    configValue "url" options.endpoint ++
    configValue "proto" (if options.endpoint == anthropicEndpoint then "=https" else "=http") ++
    configValue "proxy" "" ++ configValue "noproxy" "*" ++
    configValue "request" "POST" ++ configValue "retry" "0" ++
    configValue "max-redirs" "0" ++ configValue "max-time" (seconds options.timeoutMs) ++
    configValue "max-filesize" (toString options.responseBytes) ++
    configValue "header" "Content-Type: application/json" ++
    configValue "header" "anthropic-version: 2023-06-01" ++
    configValue "header" "Expect:" ++
    (match key with | some secret => configValue "header" ("x-api-key: " ++ secret) | none => "") ++
    configValue "data-raw" payload ++
    configValue "write-out" "\n%{http_code}"

private def decodeComplete (result : ProcessIO.CaptureResult) (maximum : Nat) : HttpObservation := Id.run do
  if result.stdoutTotal > maximum + 4 then
    return .uncertain "model response exceeded byte limit; provider usage unknown"
  if result.exitCode != some 0 then
    return .uncertain "HTTP transport did not complete; provider usage unknown"
  let bytes := result.stdout
  if bytes.size < 4 then
    return .uncertain "HTTP status frame missing; provider usage unknown"
  let start := bytes.size - 4
  if bytes[start]! != 10 then
    return .uncertain "HTTP status frame invalid; provider usage unknown"
  let some statusText := String.fromUTF8? (bytes.extract (start + 1) bytes.size)
    | return .uncertain "HTTP status frame invalid; provider usage unknown"
  let some status := statusText.toNat?
    | return .uncertain "HTTP status frame invalid; provider usage unknown"
  if status < 100 || status > 599 then
    return .uncertain "HTTP status unavailable; provider usage unknown"
  let some body := String.fromUTF8? (bytes.extract 0 start)
    | return .uncertain "HTTP response is not valid UTF-8; provider usage unknown"
  return .complete status body

/-- Execute one bounded request. No response prefix or stderr authorizes model work.
Every error after launch is conservatively interrupted/uncertain; no retry occurs. -/
def transport (payload : Json) (options : Options := {})
    (onBody : ByteArray → IO Unit := fun _ => pure ())
    (startedMs : Option Nat := none) : IO HttpObservation := do
  let started := startedMs.getD (← IO.monoMsNow)
  if options.timeoutMs == 0 then return .interrupted
  if options.timeoutMs > 3600000 || options.responseBytes == 0 || options.responseBytes > maximumBytes then
    return .failure .invalidRequest "invalid HTTP timeout or response byte limit"
  if options.endpoint != anthropicEndpoint && !isLoopbackEndpoint options.endpoint then
    return .failure .invalidRequest "endpoint must be Anthropic Messages or numeric HTTP loopback"
  if !options.cancelPath.isEmpty && (← (System.FilePath.mk options.cancelPath).pathExists) then
    return .interrupted
  let mut key := none
  if options.endpoint == anthropicEndpoint then
    let some secret ← IO.getEnv "ANTHROPIC_API_KEY"
      | return .failure .authentication "ANTHROPIC_API_KEY is not set"
    if secret.isEmpty || secret.utf8ByteSize > 4096 ||
        !secret.toList.all (fun c => 33 ≤ c.toNat && c.toNat ≤ 126) then
      return .failure .authentication "ANTHROPIC_API_KEY has an invalid format"
    key := some secret
  let encoded := payload.compress
  if encoded.utf8ByteSize > maximumBytes then
    return .failure .invalidRequest "HTTP request exceeds adapter byte limit"
  let configuration := curlConfig encoded options key
  -- Curl 8.2+ limits a configuration line to 10MB. Leave headroom for quoting
  -- and options, and reject oversized input before any process/network dispatch.
  if configuration.utf8ByteSize > 8 * 1024 * 1024 then
    return .failure .invalidRequest "encoded HTTP request exceeds transport configuration limit"
  -- Withhold the final four bytes until curl's status footer is validated. The
  -- callback sees only body bytes, even when chunks split the footer arbitrarily.
  let tail ← IO.mkRef ByteArray.empty
  let received ← IO.mkRef (0 : Nat)
  let observe := fun (chunk : ByteArray) => do
    let total := (← received.get) + chunk.size
    received.set total
    if total > options.responseBytes + 4 then
      throw (IO.userError "HTTP response byte limit exceeded")
    let bytes := (← tail.get) ++ chunk
    let retained := min 4 bytes.size
    let body := bytes.extract 0 (bytes.size - retained)
    tail.set (bytes.extract (bytes.size - retained) bytes.size)
    if !body.isEmpty then onBody body
  try
    let result ← ProcessIO.capture {
      cmd := "/usr/bin/curl"
      -- --disable MUST be first: an ambient curlrc could enable retries or logging.
      args := #["--disable", "--config", "-"]
      input := configuration.toUTF8
      timeoutMs := options.timeoutMs
      startedMs := some started
      invocationDeadlineMs := options.invocationDeadlineMs
      cancelPath := options.cancelPath
      includeHome := false
      stdoutBytes := options.responseBytes + 4
      stderrBytes := 4096
      onStdout := observe }
    match result.status with
    | .completed => return decodeComplete result options.responseBytes
    | .failedToStart => return .failure .transport "HTTP transport could not start"
    | .timedOut => return .uncertain "unexpected sandbox timeout result from HTTP transport"
    | .interrupted => return .interrupted
    | .uncertain => return .uncertain "HTTP transport cleanup incomplete; provider usage unknown"
  catch _ =>
    -- Exception and curl diagnostics can contain configuration; never expose them.
    return .uncertain "HTTP transport failed; provider usage unknown"

/-- One streaming request. Text callbacks are provisional and must enqueue into a
bounded nonblocking sink: they must never wait for a terminal/event subscriber.
Only successful HTTP completion plus a valid terminal stream reaches normalization.
A truncated limit response can preserve validated terminal usage, but no partial
content or tool call is admitted. Failed transport cannot report exact usage. -/
def request (model : ModelRequest) (options : Options := {})
    (onText : String → IO Unit := fun _ => pure ()) : IO ModelObservation := do
  let started ← IO.monoMsNow
  let decoder ← IO.mkRef ({maximumBytes := options.responseBytes} : SSE.State)
  let parseError ← IO.mkRef (none : Option String)
  let observe := fun (chunk : ByteArray) => do
    if (← parseError.get).isSome then return
    match SSE.feed (← decoder.get) chunk with
    | .error message => parseError.set (some message)
    | .ok (next, text) =>
      decoder.set next
      for piece in text do
        if !piece.isEmpty then onText piece
  match ← transport (Provider.encodeRequest model true) options observe (some started) with
  | .complete status body =>
    if status != 200 then return Provider.normalizeHttp status body
    if let some message ← parseError.get then return .failure .malformed message
    let state ← decoder.get
    if let some kind := state.serverError then
      return .failure kind "provider stream failed; usage unknown"
    match SSE.finish state with
    | .error message => return .failure .malformed message
    | .ok message => return Provider.normalizeResponse message
  | .failure kind message => return .failure kind message
  | .interrupted => return .interrupted
  | .uncertain message => return .uncertain message

end Harness.ProviderIO
