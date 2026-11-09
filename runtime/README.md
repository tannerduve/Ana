# IO boundary

The executable calls typed Lean IO functions directly. There is no Python runtime
or helper protocol. The pure core selects each operation; IO returns its observation.
Permissions, retry decisions, and budget admission remain in the core.

| Module | External operation |
| --- | --- |
| `FilesystemIO` | Bounded listing, reads, search, exact edits, and creation |
| `ProcessIO` | Launch, pipe collection, deadlines, cancellation, and cleanup |
| `ProviderIO` | One HTTPS request through `/usr/bin/curl` |
| `ApprovalIO` | Read an exact answer from the controlling terminal |
| `JournalIO` | Validate, append, and flush session records |

[The Rust static library](native/src) wraps Linux descriptors, process creation,
signals, polling, and OpenSSL SHA-256. Lean calls it directly through the C ABI;
there is no handwritten C shim. It contains no JSON handling or agent decisions.
Process creation uses glibc's `posix_spawn`, including working-directory and
descriptor-closing extensions; missing support is a launch failure. The supported
target is x86_64 Linux/glibc. Rust, the Lean compiler/runtime, glibc, libcrypto,
curl, and the OS are trusted dependencies; Lean IO is outside the core proofs.

Lake runs `cargo build --locked --release` using Rust 1.97.1 and the checked-in
lockfile (`libc` 0.2.189), placing the static library in `.lake/build/rust-native`.
`cargo` and `lean` must be on `PATH`. [lean.rs](native/src/lean.rs) mirrors the
pinned Lean 4.33.1 object layouts and ownership rules using unsafe Rust. Its build
guard checks the target, Lean version, exact runtime headers, and mimalloc
configuration. A Lean upgrade requires ABI review; a successful proof build alone
does not validate these layouts. See the [Lean FFI reference](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/).

Expected OS errors become typed Lean IO errors. Unexpected Rust panics abort the
process instead of crossing the ABI or being mistaken for an ordinary failure
after a side effect. Release builds use `panic = "abort"`; the boundary also
aborts caught unwinding panics in other profiles. An already-dispatched operation
then retains an unresolved journal intent. This does not promise cleanup after
abrupt death. [Rust's panic boundary rules](https://doc.rust-lang.org/std/panic/fn.catch_unwind.html)
describe why catching an unwind is distinct from catching every abort.
Process cleanup also uses Linux `/proc` to inspect group members, with bounded
scans. Incomplete inspection is an uncertain outcome. The exited leader remains
unreaped until signaling finishes, preventing its process ID from being reused.

Tool observations distinguish success, failure, interruption, and uncertainty.
A nonzero process exit is a completed operation with an exit code. A failed
launcher is a failure. Interrupted processes and failed mutation persistence can
leave side effects and must not be treated as safe to repeat.

Tool arguments are described by the Lean static registry. Direct paths must be
relative to the workspace; parent traversal and absolute paths are refused.
Directory traversal uses descriptor-relative `O_NOFOLLOW` opens. Symlinks are
never followed. Reads require regular UTF-8 files; directory entries with invalid
UTF-8 names produce an error instead of a lossy path alias. Listing and search walk in
sorted order, skip `.git`, `.lake`, `node_modules`, and `__pycache__`, and stop at
10,000 visited entries or depth 64. Search is literal and accepts a file or
directory; its scan budget is 64 MiB. Case-insensitive search folds ASCII letters;
other Unicode characters match literally. File content is limited to 8 MiB.

Edits require a SHA-256 preimage and exactly one nonempty matching span. Atomic
replacement and creation synchronize the new file and parent directory. Edits
assume one workspace writer: a preimage check is not an atomic filesystem
compare-and-swap operation. Creation without overwrite uses an atomic hard-link
installation that fails if the target already exists. Parent directories must
already exist. The configured workspace itself must not be a symlink.

Processes receive an argument array and a descriptor-validated working directory.
Their inherited environment is limited to `HOME`, `PATH`, `LANG`, `LC_ALL`, and
`TMPDIR`. The model cannot set environment variables through the tool schema.
A working directory is **not a sandbox**:
commands have the operating-system privileges of the harness user. Processes
run in their own process group. Both pipes are drained; deadlines, cancellation
files, and SIGINT/SIGTERM initiate TERM, then KILL, and direct-child reaping.
A residual group after leader exit produces `uncertain`. Descendants that detach
into another process group, or survive abrupt harness death such as SIGKILL,
require stronger OS isolation. Abrupt death can leave an unresolved intent;
a returned uncertain observation also requires recovery.

Output retains a bounded display prefix (default 64 KiB, maximum 1 MiB) and,
when configured, a local artifact prefix of at most 16 MiB. Truncation is
explicit. Artifacts contain raw bytes; the display uses UTF-8 replacement for
malformed or split input. Artifacts remain in the session directory until the
user removes the session; there is no automatic retention cleanup. The initial
CLI does not expose an artifact retrieval tool, so a user can inspect the
referenced local path directly.

HTTP uses one curl process without redirects or retries. Credentials come only from
`ANTHROPIC_API_KEY`; they are sent only to the fixed Anthropic Messages endpoint.
An explicit numeric HTTP loopback endpoint supports fake-server tests and receives
no API key. Set the frozen `testEndpoint` configuration field to use it; other
endpoint overrides are rejected. Headers and the body go through stdin, never command arguments or a
temporary file. Curl configuration files and proxy variables are disabled.
Response bytes are bounded. The process supervisor checks cancellation throughout
the request; its deadline covers connect, upload, and response. Transport loss and
incomplete responses report unknown outcome. Streaming progress remains deferred.

Approval polls `/dev/tty` with cancellation/deadline checks. Only the exact line
`yes` approves; EOF, unavailable terminal, or another answer denies. The Lean
core binds the observation to the exact displayed operation and configuration.

## Context and compaction

The authoritative `history` retains accepted task messages and tool results.
`activeView` can replace an older prefix in the next request with a summary;
`summaries` retains each accepted summary's source range and complete response.
Compaction runs between completed tool batches. Its request keeps the frozen
instructions, adds an explicit summary instruction, and omits tools from the
provider request. Summary attempts and retries use the same model-attempt ledger
as task inference.

| Configuration | Default | Meaning |
| --- | --- | --- |
| `compactionEnabled` | `true` | Attempt compaction when a valid source and suffix fit. |
| `compactAtPercent` | `75` | Trigger relative to `maxContextBytes`; interpreted within 1–99. |
| `compactionKeepMessages` | `4` | Retain at least this many recent raw messages, with a minimum of two and valid tool pairing. |
| `maxSummaryBytes` | `12000` | Maximum UTF-8 bytes in accepted summary text. |
| `maxContextBytes` | `200000` | Conservative request-byte allowance, including 16 KiB for schemas and framing. This is not a provider token bound. |

A complete summary must contain nonempty text and no tool calls. The core checks
the reconstructed task context's size and tool-result pairing before installing
it. Rejection, interruption, or failure preserves the previous active view;
configured transient failures may retry within the attempt limit. If no usable
view fits, the session stops explicitly. These checks establish structure, not
summary fidelity or successful completion of a long task. Raw history and summary
records still grow, and the journal limit below still applies.

## Persistence and recovery

Journal frames include a version, contiguous sequence number, previous hash,
record, and SHA-256 checksum over canonical JSON. Each append fsyncs the file
and parent directory. Hashes detect corruption, not a malicious writer.
An incomplete last line preserves the valid prefix and prohibits append.
Invalid complete frames refuse replay. Total journal size is limited to 64 MiB
in this initial adapter. Whole-journal reads and validation on each append
favor a small reviewable implementation over long-session performance.
The filesystem must honor file and directory `fsync`; network filesystem
durability is not claimed. Journal guarantees also depend on the Lean runner
holding its session lock and recording intent before dispatch.

Session and state schemas are now version 2; journal framing remains version 1.
The executable hash also binds resume to the same build. Version-1 sessions and
sessions from another executable require their original build; there is no
automatic migration. The fingerprint covers the executable, including statically linked
dependencies; it does not identify curl or dynamically linked system libraries.

Sessions default to `$XDG_STATE_HOME/lean-harness/sessions`, or
`~/.local/state/lean-harness/sessions`. Session storage and workspace paths must
not contain one another, including through symlinks. This keeps direct file tools
away from the journal. Approved processes still have the user's OS permissions.
Resume rechecks the workspace path; offline inspect/replay works even if it is gone.

Before an edit can dispatch, the runner records its path, expected preimage hash,
and intended postimage hash with the intent. Recovery distinguishes these cases:

| Saved state | Resume behavior |
| --- | --- |
| Durable completed observation | Replay the observation without repeating the operation. |
| Uncertain edit whose current bytes match the postimage | Recheck through no-follow descriptors, fsync the file and parent, record a resolution, then continue the original batch. |
| Edit still matching the preimage | Stop: it may be unstarted or have had no lasting effect. Never infer that rerunning is safe. |
| Conflicting edit contents, missing witness, or unsafe path | Stop for manual investigation. |
| Uncertain process | Require an explicit operator resolution. No command is automatically repeated. |
| Other unresolved intents, or an incomplete journal tail | Refuse automatic resume. |

Postimage reconciliation establishes the observed desired contents under the
single-writer and filesystem durability assumptions. It does not establish that
the edit executed exactly once. It also handles a recorded uncertain/interrupted
edit completion. The replay cursor retains the pre-operation batch position,
including reserved counts and remaining calls.

Inspect a process recovery stop, then supply its exact `recoverableOperation` ID:

```sh
harness inspect SESSION
harness resolve SESSION --operation 7 --status completed --exit-code 0 \
  --note 'Inspected the result and confirmed the original processes have stopped' \
  --resources-settled
harness resume SESSION
```

Use `--status abandoned` without `--exit-code` when the outcome remains unknown.
The nonempty note is limited to 2048 bytes; completed exit codes must be in 0–255.
`--resources-settled` is an operator assertion that the original process and its
descendants can no longer act, not an OS check. Resolution writes a distinct
journal record with operator provenance and an explicitly unverified result. It
executes no command and does not resume inference; `resume` is a separate action.
An abandoned result preserves the uncertainty of prior effects. Wrong operation
IDs and repeated resolutions are rejected. Cancellation markers are not silently
cleared by either command.

For a planned restart, `run` and `resume` accept `--yield-after N`. After N durable
completions in that invocation, the runner emits `suspended` and exits 75 with no
pending intent or terminal record. A task that has already finished reports its
outcome instead. Zero disables this scheduling limit. For example:

```sh
harness run --workspace PATH --config CONFIG --task TEXT --session SESSION --yield-after 12
harness inspect SESSION
harness resume SESSION --yield-after 12
```

Repeated resumes preserve cumulative call counts and frozen configuration; each
invocation gets a fresh elapsed-time allowance. Yielding itself does not create
a model or tool attempt.

## Deterministic validation

Tests use Python 3, a C compiler for injected syscall failures, and `sha256sum` as
an independent hash oracle. The C fault fixtures are test-only. The ABI suite
crosses the actual Lean/Rust boundary 10,000 times per case, covering binary and
empty buffers, Unicode, borrowed values, large boxed integers, nonblocking
`none` versus empty EOF, and descriptor counts. It is regression evidence, not a
proof of memory safety:

```sh
lake build
cargo fmt --manifest-path runtime/native/Cargo.toml --check
cargo clippy --locked --all-targets --manifest-path runtime/native/Cargo.toml --target-dir .lake/build/rust-native -- -D warnings
cargo test --locked --manifest-path runtime/native/Cargo.toml --target-dir .lake/build/rust-native
lake exe harness_tests
lake exe runtime_properties
python3 Tests/runtime_contracts.py
python3 Tests/native_abi.py
python3 Tests/provider_transport.py
python3 Tests/integration.py
python3 Tests/crash_recovery.py
python3 Tests/session_boundaries.py
python3 scripts/check_core.py
```

The [sustained-session gate report](../eval/reports/2026-11-09-sustained-gates.md)
records the compaction/restart and recovery checks for schema 2. Streaming,
model-accessible artifact retrieval, broader uncertain-effect recovery,
automatic storage repair, and OS sandboxing remain outside this implementation.
