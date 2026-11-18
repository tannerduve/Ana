# IO boundary

The pure Lean core chooses an operation. Lean IO performs it and returns a typed
observation. The executable requires no Python runtime or helper agent loop.

| Module | Responsibility |
| --- | --- |
| `ApplicationIO`, `Applications/*IO` | Typed application execution, input validation and reconciliation |
| `FilesystemIO` | Bounded listing, reads, search, exact edits and creation |
| `ProcessIO`, `Sandbox` | Process supervision and the optional Linux isolation profile |
| `ProviderIO`, `SSE` | One streaming Anthropic request and validated response assembly |
| `ArtifactIO` | Immutable output storage and checked ranged retrieval |
| `ApprovalIO`, `EventIO` | Exact-action approval and bounded terminal/JSONL output |
| `JournalIO`, `Runner` | Durable intent/completion records, replay and recovery |

[The Rust library](native/src) supplies Linux descriptors, process primitives,
signals, polling and OpenSSL SHA-256 through Lean's C ABI. There is no handwritten
C shim. Lake builds it with pinned Rust and Cargo dependencies. Its build guard
checks the x86_64 Linux/glibc target and exact Lean runtime headers. Unsafe ABI
conversions, Lean IO, curl, dynamically linked libraries and the OS remain outside
the core proofs. Unexpected native panics abort; an unfinished intent then remains
for recovery.

## Files and processes

Direct file tools accept workspace-relative paths and reject symlink traversal
with descriptor-relative `O_NOFOLLOW` opens. Listing and search use stable ordering,
skip `.git`, `.lake`, `node_modules` and `__pycache__`, and stop at 10,000 entries or
depth 64. Search is literal, scans at most 64 MiB, and optionally folds ASCII case.
Files must be regular UTF-8 files of at most 8 MiB.

Edits require a matching SHA-256 preimage and exactly one matching nonempty span.
Replacement and creation synchronize the new file and its directory. Parents must
already exist. Direct edits assume a single writer: a preimage check does not lock
out concurrent replacement.

Processes take an argument array and a checked working directory. They run in a
separate process group. The supervisor drains both pipes, checks deadlines and
cancellation, sends TERM followed by KILL when necessary, and reaps the child.
Nonzero exit status is a completed command. Failed launch, interruption and
uncertain cleanup have distinct observations. Completion and cancellation races
are decided by the observation the supervisor returns; a later consumed control
cancellation still stops admission of further work.

Operation clocks include request preparation. The absolute invocation deadline
also survives encoding, path checks and sandbox setup and is checked before
launch. These checks are cooperative: they cannot preempt a blocked OS call.
Startup/resume validation has its own allowance before the invocation clock starts.

A local command deadline can return `timedOut` under `bubblewrap` once the
adapter establishes that the sandboxed attempt has stopped. Partial effects may
remain. The core records an error, skips the remaining queued calls, and checks
control before another model request. It never automatically repeats the command.
Retained partial results carry no asserted target exit code or file hash.
Cancellation, the overall invocation deadline, host execution and uncertain
cleanup keep their conservative interruption/recovery behavior.

| `executionProfile` | Access and assumptions |
| --- | --- |
| `host` (default) | Commands have the harness user's OS privileges. Filtering environment variables and setting the working directory do not contain them. Detached descendants can outlive the supervised group. |
| `bubblewrap` | Commands see the workspace, read-only system/toolchain trees, private `/tmp` and home, and separate process/network/user namespaces. Capabilities are dropped. Other host-home contents, session storage and unrelated inherited descriptors are absent. |

The isolated profile requires `/usr/bin/bwrap` with `--bind-fd`, `--ro-bind-fd`,
`--ro-bind-data`, `--json-status-fd` and `--disable-userns`, plus host permission to create the
namespaces. Ubuntu's patched `0.9.0-1ubuntu0.3` is tested; an upstream version
number alone does not establish feature compatibility. Startup performs a real
profile probe and fails if it cannot run. There is no automatic host fallback.

Timeout settlement requires a trusted namespace-init receipt, closed output
pipes, no live member in the monitored group, and a successful reap. It relies on
the fixed bubblewrap process graph and Linux terminating namespace descendants
before init exits. The host must provide complete visibility of owned processes
through procfs in the caller's PID namespace; startup and dispatch reject a
mismatched view. Missing receipts or failed cleanup cannot establish settlement.
The receipt alone does not establish that the target program launched.

Fixed read-only `/etc/hosts` and `/etc/nsswitch.conf` files resolve `localhost`
inside the private network namespace. Local test servers can communicate within
one command's sandbox; external networking remains disabled. Host `/etc` is not mounted.

The same opened workspace is mounted at its canonical path and `/workspace`, so
editable installations retain their paths. Reserved-path collisions are rejected.
A bounded startup/resume scan rejects hardlinks, special files, escaping symlinks
and externally linked Git worktrees. Use a disposable, independent checkout
with its own `.git` directory; `git clone --no-local SOURCE DESTINATION`
creates one from a local repository. Internal symlinks are supported by sandboxed
commands; direct file tools still reject symlinks. Subsequent commands assume no
concurrent external workspace writer and settled previous commands.

`toolchainRoots` lists up to eight canonical, operator-trusted installation trees
with `bin` directories. They are mounted read-only at fixed paths under
`/opt/harness/toolchains`; their `bin` directories precede `/usr/bin:/bin` on PATH.
Their contents must not contain secrets. The profile does not impose CPU, RAM or
disk quotas, provide a hostile multi-tenant boundary, or reverse side effects.

## Output and artifacts

Tool content previews use `maxToolOutputBytes` (default 64 KiB); artifact references
and diagnostics add metadata. Large or
interrupted process output can retain separate raw stdout/stderr artifacts.
`maxArtifactBytes` defaults to 16 MiB and `maxSessionArtifactBytes` to 64 MiB;
CLI ceilings are 16 MiB and 256 MiB respectively. Truncation is explicit, including
when the storage allowance is exhausted. Orphaned output bytes count against it.
Metadata has separate 4 KiB record and 4,096 directory-entry bounds and does not
consume the output-byte allowance.

The `artifact` tool accepts an admitted opaque ID, byte offset and length of
1–65,536 bytes. The core checks session membership; IO verifies immutable metadata,
regular-file/link constraints, length and SHA-256 before returning a bounded range. Invalid UTF-8
ranges use hex encoding. The registry survives compaction and restart. Data and
metadata are flushed before a completion references them. Artifacts remain local
until the user removes the session; there is no automatic retention cleanup.

`--json` emits JSONL events separately from human diagnostics. Streaming text is
marked provisional and cannot authorize a tool. Event queues are bounded; a slow
pipe or terminal cannot indefinitely block the agent. Lost output is reported,
and an otherwise successful invocation exits 74 when output delivery fails. The
durable task outcome is unchanged. Large inspect output has a bounded delivery
window. Regular-file output still depends on filesystem responsiveness.

## Provider and approvals

`modelBackend` selects `anthropic` (the default), `claude-code`, or `codex` and is
frozen with the session configuration. The CLI backends use the installed official
executables and their saved sign-in; the harness never reads OAuth credentials.
See the [quickstart](../README.md#getting-started) and example configs for login
and invocation commands. The following HTTP transport description applies to the
`anthropic` backend.

CLI backends start a fresh process in private scratch outside the application
workspace and session, then normalize structured proposals into the same typed
model observation consumed by the engine. The installed executable must also be
outside those roots. CLI authentication, internal retries and schema generation
are trusted adapter behavior. A model-attempt reservation counts one CLI
invocation, not each upstream inference request. Output bytes and elapsed time
are enforced locally; `maxOutputTokens` is advisory for CLI backends. Progress is
buffered until completion, and native CLI sessions are not resumed. Harness
journal replay, follow-ups, permissions and cumulative tool budgets still apply.

One curl invocation performs one provider attempt, with redirects and hidden
retries disabled. Credentials come from `ANTHROPIC_API_KEY` and go only to the
fixed Anthropic endpoint through stdin configuration. Ambient curl configuration
and proxy variables are suppressed. A frozen numeric-loopback `testEndpoint`
supports local fixtures and receives no API key.

The streaming parser bounds buffered bytes and validates the entire message
lifecycle, content blocks, call identities, stop reason and usage before accepting
an authoritative response. Incomplete responses execute no tools. Transport loss
can leave usage unknown even if the provider processed the request. The deadline
covers the full transfer; provisional text is only a display event.

`maxResponseRepairs` defaults to two per session. A malformed/truncated task
response or rejected complete tool batch can receive fixed, bounded feedback and
a fresh model attempt after a cancellation check. Rejected content stays outside
accepted history. Repairs consume the normal model-attempt allowance and retain
known or unknown usage; their separate counter survives replay and restart.
Set the limit to zero to stop on the first such error. Summary failures and
network retries keep their separate policies.

Before Lean parses provider or journal JSON, a lexical scan limits nesting to
128 containers, numeric literals to 4,096 digits, exponent magnitude to 4,096 and
cumulative numeric work to 1,048,576 decimal digits. Stream events and their tool-argument reparses
share that work budget. Quoted text is unaffected. This prevents short numeric
inputs from requesting enormous integer expansions; grammar checking still uses
Lean's parser. These limits do not constitute a memory or time guarantee.

The session-wide `toolPolicy` is an additional ceiling for every application. Either a global or application denial prevents dispatch; either approval requirement demands an exact grant. Coding also applies its `commands` policy to processes.

`capabilityPolicy` adds resource ceilings checked by the core before a tool action
or approval is emitted. All required accesses must be covered; approval cannot
override denial. `--restrict-capabilities FILE` appends a ceiling at session
creation. `policy check PARENT CHILD` and `policy restrict PARENT LIMIT` inspect or
compose policy files without a provider. See [scoped permissions](../docs/Capabilities.md).
File scopes apply to the dedicated file tools, not to effects of an authorized
process. The process sandbox still exposes its declared workspace mounts.

Approval uses the controlling terminal, with deadline and cancellation checks.
Only the exact line `yes` approves. Unavailable terminal, EOF or any other answer
denies. The grant binds the exact operation and frozen configuration and is used
once. If the full approval prompt cannot be delivered, approval is not accepted.
Approval metadata is ASCII-escaped JSON, so control characters cannot reorder or
erase the displayed workspace, profile or arguments.

## Context

The authoritative transcript retains accepted task messages and results. A separate
active view can replace an older prefix with a summary and retain a protocol-valid
recent suffix. Summaries run at completed tool-batch boundaries, preserve frozen
instructions, omit tools, and consume the same attempt budget as task inference.

Each task request includes a notice of remaining model/tool calls, the output
limit and the configured operation duration. Cleanup may take additional time;
the remaining invocation deadline can shorten the operation limit.
The current model attempt is already reserved. The notice is reconstructed
from the ledger, included in context admission, and kept out of raw history and
summary source material.

| Setting | Default |
| --- | --- |
| `compactionEnabled` | `true` |
| `compactAtPercent` | `75` |
| `compactionKeepMessages` | `4` |
| `maxSummaryBytes` | `12000` |
| `maxContextBytes` | `200000` |

Admission uses request bytes, including the artifact catalog, budget notice, actual offered schemas and a framing
allowance; it is not an exact token ceiling. A summary must be complete, nonempty,
tool-free and fit the reconstructed request. Failure leaves the previous view
intact. If no usable view fits, the session stops. Structural checks do not
establish summary fidelity. Raw history and the journal continue to grow.

## Persistence and recovery

Journal frames contain sequence numbers and chained SHA-256 checksums over
deterministically serialized JSON. The runner holds a single-writer lock, flushes intent before
dispatch, and flushes completion before consuming the observation. It executes
the pure [persistence protocol](../Harness/Core/Persistence.lean); its proofs
require matching successful acknowledgments before dispatch and advancement.
Appends synchronize the file and directory. This assumes a filesystem honoring `fsync`;
network-filesystem durability and malicious journal writers are outside the
contract. Checksums detect damage, not forgery.

Before writing a frame, the runner reparses its bounded encoding and checks Lean's
JSON value equality against the original. The pinned JSON printer cannot preserve
every accepted numeric representation. Such a frame is refused with
`journal value cannot be serialized losslessly`; the durable prefix remains intact
and the core does not consume the unwritten observation. Any earlier intent stays
pending and follows the usual uncertain-operation recovery rules.

State/session schema is **7**; frame schema remains **1**. Resume requires the
identical executable, installed application ID/version and frozen configuration. Older sessions require their
original binary; there is no guessed migration. The executable fingerprint does
not identify dynamically linked libraries or curl.

For coding sessions, session storage must be outside the workspace. It defaults to
`$XDG_STATE_HOME/lean-harness/sessions`, or `~/.local/state/lean-harness/sessions`.
Resume checks its saved canonical location and the selected application's resource assumptions. Inventory uses frozen starting data plus its session-local reservation ledger and requires no workspace. Offline
inspect/replay may examine a copied session without dispatching effects.

| Saved condition | Recovery |
| --- | --- |
| Durable completion | Replay its observation without repeating the effect. |
| Durable settled timeout | Replay the error and skipped-call results; continuation requires no operator resolution. A lost timeout completion remains an uncertain process. |
| Lost control or approval | Clear the old grant and observe control again; request a fresh approval if needed. |
| Lost retry wait | Start a fresh cancellable wait. |
| Lost model response | Retain the reserved attempt, mark unknown usage, and apply bounded retry policy. |
| Lost operation classified as read-only by the application | Record an unknown-result error for that call. A later model decision may request a new read. |
| Uncertain edit matching its intended postimage | Recheck through no-follow descriptors and synchronize before recording reconciliation. |
| Inventory reservation with a matching durable receipt | Validate and synchronize the receipt, then resolve without debiting stock again. Missing or conflicting evidence leaves it unresolved. |
| Other uncertain edit/create | Require explicit abandonment after inspection; never blindly repeat it. |
| Uncertain process | Require explicit operator resolution and assertion that original resources are settled. |
| Torn tail or invalid record | Preserve evidence and refuse automatic advancement. |

Postimage reconciliation establishes the observed desired contents under the
single-writer assumption, not exactly-once execution. Resolution is a separate
administrative transition and labels operator assertions as unverified. Final
answers, failures, cancellations and limit stops cannot be reopened through it.

```sh
harness inspect SESSION
harness resolve SESSION --operation 7 --status completed --exit-code 0 \
  --note 'Inspected the result and confirmed the original processes stopped' \
  --resources-settled
harness resume SESSION
```

Use `--status abandoned` without an exit code when the effect remains unknown.
For uncertain file mutations, abandonment requires a note but no process-resource
assertion. Resolution itself runs no command or inference.

For planned restarts, `run`, `resume` and `continue` accept `--yield-after N`. Exit 75 means the
invocation stopped after durable completions without an unresolved operation.
Resume preserves cumulative counts and admits a fresh elapsed-time allowance.

Journals have a 64 MiB ceiling. A writer validates the prefix once when opened
under the session lock, then retains its sequence number, checksum and byte count.
An append checks file identity and size, writes and synchronizes the new frame,
then advances the cursor. Any failure invalidates the writer; reopening must
validate the prefix again. Calls on a writer are sequential and session storage
must have no concurrent external writer. Same-size external rewrites are outside
that assumption. Compatibility callers without a retained writer still validate
on every append. There is no snapshot acceleration or automatic torn-tail repair. See
[the safety evidence](../docs/Safety.md), [CI](../.github/workflows/ci.yml), and
[the optional capacity measurement](../Tests/journal_scale.py) for validation.

## Follow-up turns

```sh
harness continue SESSION --task 'Use the earlier results to complete the next step'
```

`continue` adds trusted user input after a durably finished or settled cancelled
turn. `resume` continues unfinished work. Pending intents, uncertain effects and
unclosed transcripts block follow-up admission; resolve or recover them first.
Failure and exhausted-limit outcomes do not become fresh allowances through this
command.

A follow-up preserves the frozen configuration, raw history, active context,
artifacts, seen call IDs and every spent session counter. It clears approval and
transient retry state. The user-turn record is durable before execution starts.
Repeated or stale turn records are rejected. Turn IDs start at zero and appear in
structured events and inspection.

Cancellation before tool dispatch records each remaining admitted call as not
executed, in order. An interrupted tool may have acted and still requires recovery.
`cancel SESSION` targets the turn observed in the journal and reports its ID;
it can be called while execution holds the session lock. A concurrently admitted
follow-up may be a different turn. Existing cancellation markers are retained and
never silently reassigned or deleted to start new work.

Model/tool ceilings apply to the whole session, including summaries and retries.
Each invocation receives a fresh elapsed-time allowance. The finite-reply theorem
applies to each user turn with its remaining budget, not an indefinitely supplied
sequence of user tasks.
