# Safety requirements and evidence

The execution boundary must hold even when model output, repository text and tool
output are adversarial. Such content may propose an operation; it must not grant
permission, replace the frozen configuration, manufacture an approval, or turn an
incomplete response into an executable batch. This is a requirement about the
harness's authority checks. It does not establish that a permitted operation is
wise, that a model answer is true, or that prompt injection has been solved.

The approval channel, initial configuration, executable and session storage are
trusted inputs. An attacker who can forge approval observations or rewrite the
journal is outside the present model. Journal checksums detect damage, not an
adversary able to recompute them. An approved process has its operating-system
permissions; a repository working directory is not a sandbox.

The following cases motivate concrete requirements. The first three are vendor
security advisories about historical affected versions. The last two are original
user reports, included as regression scenarios rather than independently verified
accounts or claims about current versions.

| Failure case | Requirement for this harness |
| --- | --- |
| Claude Code's `find` command parsing allowed execution without the expected approval. [GHSA-qgqw-h4xq-7w8w](https://github.com/anthropics/claude-code/security/advisories/GHSA-qgqw-h4xq-7w8w) | Approve the complete typed operation, arguments and working directory. Recheck the grant at dispatch. A harmless-looking executable name is not an authorization rule: programs such as `find`, interpreters and build tools can launch other programs. |
| Repository settings could redirect API calls and credentials before trust confirmation. [GHSA-jh7p-qr78-84p7](https://github.com/anthropics/claude-code/security/advisories/GHSA-jh7p-qr78-84p7) | Repository content cannot select the authenticated provider endpoint. Use the fixed Anthropic URL, omit credentials from loopback tests, suppress ambient curl configuration, and do not load repository hooks or credential helpers automatically. |
| An Edit implementation checked paths, then followed a replaced parent directory during writing. [GHSA-5xjx-9qx6-jcrv](https://github.com/anthropics/claude-code/security/advisories/GHSA-5xjx-9qx6-jcrv) | Bind direct file access to opened directory descriptors and reject symlink traversal. Check the expected preimage and replace atomically. Lexical path checks alone are insufficient. Concurrent directory mutation and file replacement still require explicit operating-system assumptions and tests. |
| A report describes tool completions starting new inference after cancellation. [Issue #26802](https://github.com/anthropics/claude-code/issues/26802) | Consumed cancellation must terminate the turn. Physical process cleanup is a separate obligation; late completion must not silently restart work. |
| A report describes interrupted agents restarting from empty transcripts and repeating completed paid operations. [Issue #88993](https://github.com/anthropics/claude-code/issues/88993) | Reserve attempts durably, retain completed observations and distinguish an unresolved intent from an unstarted operation. Never blindly replay an uncertain mutation. Missing provider usage remains unknown. |

Current evidence is deliberately narrower than these requirements:

| Status | What the repository establishes |
| --- | --- |
| **Proved in Lean** | [Invariants.lean](../Harness/Proofs/Invariants.lean) proves reachable dispatch ceilings, authorization of emitted tool requests, rejection of a changed grant when approval is required, terminal behavior and termination of the turn after consumed cancellation. Accepted tool responses have consistent retained content and normalized fields, pass whole-batch validation and preserve the accepted blocks. [Configuration.lean](../Harness/Proofs/Configuration.lean) proves that every typed continuation preserves the entire configuration and every reachable state retains the initial configuration. |
| **Proved, limited replay claim** | [Recovery.lean](../Harness/Core/Recovery.lean) proves deterministic replay for the same initial state and record sequence. This is not a proof of durable writes, exactly-once external effects, or equivalence to every possible live execution. |
| **Executable tests** | [Core](../Tests/Core.lean), [provider](../Tests/Provider.lean) and [recovery](../Tests/Recovery.lean) fixtures exercise malformed batches, approval changes, usage, limits and record ordering. [Properties.lean](../Tests/Properties.lean) adds 900 Plausible-generated provider/core cases with reproducible seeds and shrinking. These properties exercise serialization and transitions; they are not IO-effect tests or proofs. |
| **Real HTTP tests** | [provider_transport.py](../Tests/provider_transport.py) calls the compiled Lean adapter against local servers. It checks escaping, credential suppression, ambient configuration, redirects, retries, incomplete/invalid bodies, output bounds, full-transfer deadlines and cancellation. No real provider or production credential is involved. |
| **Generated real IO tests** | [RuntimeProperties.lean](../Tests/RuntimeProperties.lean) passes 100 Plausible-generated Unicode filesystem/journal cases (seeds 52000–52099), including stale/ambiguous edits leaving bytes unchanged, symlink/path escapes and an independent SHA-256 oracle. Each case follows a fixed operation sequence. Failures report seed/input; this IO suite does not yet shrink automatically. |
| **Native ABI tests** | [native_abi.py](../Tests/native_abi.py) invokes the compiled Lean test driver through the real Rust boundary. Three cases repeat sensitive calls 10,000 times, checking binary/empty buffers, Unicode and borrowed inputs, boxed integers above 2³², descriptor ownership, and nonblocking `none` versus empty EOF. Independent Python oracles check hashes, metadata and process bytes. Descriptor counts do not establish heap-leak freedom or memory safety. |
| **Crash tests** | [crash_recovery.py](../Tests/crash_recovery.py) injects an intent-write failure and three actual process crashes: after durable intent, after the external effect before completion, and after durable completion. An independent counter records actual external invocations. This covers selected boundaries, not every storage failure or scheduler interleaving. |
| **Trusted adapter obligations** | Lean IO implements filesystem access, process supervision, HTTP orchestration and journal handling. Rust syscall/crypto bindings and unsafe Lean ABI conversions, curl, the Lean runtime, the OS and filesystem remain trusted. Real-process, fake-server and crash tests must validate these boundaries; changing the implementation language does not make them kernel-verified. |
| **Still needed** | A full reachable-history invariant, approval provenance across traces, comprehensive crash and hostile-filesystem tests, conditional progress arguments, explicit uncertain-edit reconciliation, tested compaction and stronger process isolation. |

Direct edits currently assume a single writer. A preimage hash does not lock out a
concurrent writer. Process groups support cancellation of cooperating local
descendants, but detached groups, remote operations and uninterruptible kernel
work need stronger isolation or an explicit uncertain outcome. Environment
filtering is not credential isolation from another process with the same OS
identity; host process visibility and file access also matter.

The Rust boundary pins Lean's runtime headers and x86_64 Linux/glibc layout;
unknown headers or targets fail the build. Borrowed inputs and owned results still
depend on correct unsafe code. Unexpected native panics abort, preserving any
uncompleted intent for conservative recovery rather than reporting a retryable
failure after a possible effect. Neither Rust's type system nor these tests prove
that the handwritten ABI matches every runtime behavior.

Session directories default to `$XDG_STATE_HOME/lean-harness/sessions`, or
`~/.local/state/lean-harness/sessions` when no absolute XDG state directory is
configured. The runner resolves existing path ancestors, including symlinks,
before rejecting either workspace/session containment direction. It checks at
creation and again before resume can dispatch work. Offline inspection and replay
remain available when the workspace is missing. This protects session storage
from the direct file tools under the stated filesystem assumptions; an approved
general process can still reach storage permitted by its OS identity.

The transport performs one curl invocation with retries and redirects disabled,
passes credentials through stdin configuration, discards transport diagnostics,
and accepts only complete bounded UTF-8 responses. Its deadline covers the full
transfer. These are implementation contracts, not a claim of exactly-once remote
processing. Provider behavior and lost responses can still leave cost unknown.

Safety and progress need separate statements. The pure `step` terminates, but
that alone does not guarantee that a run finishes. A useful future progress claim
must assume that the runner is scheduled and each IO operation either returns or
is stopped by a working deadline mechanism. Even under those assumptions,
termination may mean a limit, cancellation or recovery requirement rather than
successful task completion.

The next release gates are:

1. **Native migration:** pass the existing deterministic suite against the actual
   Lean adapters and Rust ABI, including the additional representation and
   ownership checks. Exercise fake HTTP servers, nonzero exits, large and invalid UTF-8
   output, cancellation, failed cleanup, denied paths and stale edits. Keep the
   pure generated properties separate from tests that perform real IO.
2. **Broader generated IO tests:** extend the current generated-data cases to
   bounded operation sequences against fresh temporary workspaces. Compare results and final bytes with a
   small independent model: create/read roundtrips, exact edits, stale-preimage
   rejection leaving bytes unchanged, and journal prefix recovery. Recreate the
   fixture for every shrink; record the seed and minimized sequence. A discarded
   or inconclusive run must not pass. Expand coverage with scheduled seeds while
   retaining fixed regression seeds.
3. **More fault and adversarial tests:** extend the four existing failure cases to
   additional dispatch, flush and completion interleavings. Continue counting
   external invocations independently. Race symlink replacement, interrupt both
   event orderings, test lock contention and storage failures, and verify that no
   uncertain mutation is dispatched again automatically.
4. **Sustained operation:** prove the additional history and approval properties,
   establish compaction and restart gates, then measure task success and recovery
   on a reserved workload. A plausible test run or a successful demonstration
   cannot substitute for these gates.
