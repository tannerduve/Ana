# Safety requirements and evidence

Model responses, repository files and tool output may be adversarial. They may
propose actions, but cannot grant approval, change the frozen configuration or
turn an incomplete response into executable work. The operator, approval channel,
initial configuration, executable and session storage are trusted. Checksums
detect corruption; they do not authenticate a journal against its writer.

## Core properties

Proofs concern the same pure transition definitions used by the CLI. An ordinary
execution trace records the actions returned by `step` and their typed replies.
External operations and administrative recovery have separate obligations.

[Generic coalgebra lemmas](../Harness/Theory/Coalgebra.lean) provide trace
composition, invariant propagation and bounds from decreasing ranks. They use
Mathlib's predicate lifting and reflexive-transitive closure. The harness
specializes these results in [Reachability](../Harness/Proofs/Reachability.lean)
and [Trace](../Harness/Proofs/Trace.lean); each property below still supplies its
own initialization and transition proofs. Shared
[validation contracts](../Harness/Proofs/Validation.lean) and
[successful-result rules](../Harness/Proofs/Except.lean) support batch and replay
proofs.

| Property | Evidence and scope |
| --- | --- |
| Frozen authority | [Configuration](../Harness/Proofs/Configuration.lean): every typed continuation retains the complete configuration, including provider, policy, workspace, isolation profile and limits. |
| Dispatch admission | [Invariants](../Harness/Proofs/Invariants.lean): emitted calls satisfy the executable permission predicate and reserved call ceilings. Malformed or inconsistent model batches cannot dispatch. |
| Scoped capabilities | [Capability algebra](../Harness/Proofs/CapabilityAlgebra.lean) proves restriction/intersection cannot widen authority and the finite containment checker is sound. [Dispatch](../Harness/Proofs/Capabilities.lean) requires every declared access to satisfy the frozen ceilings, including after accepted replay/recovery/follow-ups. Matching approvals cannot override a capability denial. Installed application classifications have explicit [demand contracts](../Harness/Proofs/ApplicationCapabilities.lean). These cover dedicated-tool scope and exact process invocation, not transitive process effects or information flow. |
| Bounded response repair | [Repair bounds](../Harness/Proofs/ResponseRepairBudget.lean) preserve the frozen ceiling and never refund repair credit. [Recovery](../Harness/Proofs/ResponseRepairRecovery.lean) extends this to accepted journal records and operator resolution. Repair adds fixed feedback, clears approval and requires another control check and model reservation; it does not admit rejected calls. |
| Exact, single-use approval | [Approvals](../Harness/Proofs/Approvals.lean) covers ordinary dispatch; [MixedApprovals](../Harness/Proofs/MixedApprovals.lean) covers accepted tool intents across recovery and operator resolution. Each ask-policy intent has an earlier approval for that exact call under the same configuration, with an unused grant retained throughout the intervening records. Another tool intent needs fresh approval. The approval observation itself is trusted. |
| Call identity and history | [History](../Harness/Proofs/History.lean): admitted IDs are globally unique in ordinary execution; emitted calls were admitted; an identity cannot dispatch twice. Emitted task contexts pass the tool-pairing check. |
| Open conversation prefixes | [RawPrefix](../Harness/Proofs/RawPrefix.lean): ordinary reachable states and accepted replay prefixes retain a structurally valid raw history. Active pending IDs match the remaining ordered batch. Stopped states may retain an explicitly incomplete suffix. |
| Settled command timeout | [SettledTimeout](../Harness/Proofs/SettledTimeout.lean): an eligible timeout closes the ordered batch with error results, preserves counters/configuration and retires the skipped IDs from ordinary execution without dispatch. Its durable completion leaves no operator-resolution target. Physical settlement is an adapter obligation; partial effects remain. |
| Artifact authority | [Artifacts](../Harness/Proofs/Artifacts.lean): registration preserves unique identities, immutable existing entries, metadata checks and retained-byte bounds. Emitted artifact reads name registered IDs. IO must establish that bytes match this metadata. |
| Artifact request bounds | [ArtifactBounds](../Harness/Proofs/ArtifactBounds.lean): emitted reads in ordinary execution and accepted administrative replay have a registered ID, requested length 1–65,536 bytes and an admitted dispatch count. Offsets beyond retained bytes receive typed IO errors. |
| Compaction structure | [Compaction](../Harness/Proofs/Compaction.lean): accepted summaries preserve raw history and frozen instructions, produce a bounded protocol-valid context, and consume the shared attempt budget. Failed summaries retain the previous view. Summary fidelity is measured separately. |
| Consumed cancellation and terminal states | [Invariants](../Harness/Proofs/Invariants.lean): once the core consumes cancellation, it emits no new model/tool work for that turn. A terminal state stays terminal under `step`. This does not reverse effects or prove physical cleanup. |
| Finite ordinary execution | [Progress](../Harness/Proofs/Progress.lean): each consumed reply decreases a natural-number rank. From initialization, replies are bounded by `1 + maxModelAttempts × (4 × maxBatchCalls + 3)`. Eventual termination additionally requires a scheduled runner and returning/interrupted IO. It may terminate with failure, a limit or recovery requirement. Administrative restart loops are outside this bound. |
| Follow-up turns | [Turns](../Harness/Proofs/Turns.lean): trusted user input extends only a settled transcript, clears approvals and preserves configuration, artifacts and all spent session budgets. Each new turn has a reply bound based on its remaining allowance. Cancellation closes the undispatched suffix with ordered error results. |
| Mixed operation identity | [IntentIdentity](../Harness/Proofs/IntentIdentity.lean): accepted intent IDs are strictly increasing across ordinary records, recovery, resolution and user turns. Completion and resolution records intentionally refer to existing IDs. |
| Persistence ordering | [Persistence](../Harness/Proofs/Persistence.lean): the protocol executed by the runner exposes dispatch only after the matching intent acknowledgment, and releases the saved reply only after its completion acknowledgment. Persistence failures stop the protocol. The meaning of a durable acknowledgment remains a storage-adapter assumption. |
| Application contracts | [Application laws](ApplicationContracts.md): both installed applications prove independent operation/result validity contracts, valid-value codec round trips and faithful model-visible rendering through the actual continuation. These laws do not establish the truth of external observations. |
| Journal cursor | [Journal](../Harness/Proofs/Journal.lean): the shared frame validator preserves sequence, byte-count and checksum-link bookkeeping. The retained writer advances its cursor only after successful synchronization and invalidates it on failure. Hashing, filesystem behavior and exclusive writer ownership remain assumptions. |

[Replay](../Harness/Proofs/Replay.lean) connects accepted ordinary record prefixes
to actual executions. Its recorded-trace theorem reconstructs the same final
state under explicit per-reply serialization/decoding premises.
[Administrative recovery](../Harness/Proofs/Administrative.lean) proves the joint
configuration, budget, call/result, history and artifact invariant for every
successfully replayed record list from initialization, including recovery and
operator-resolution records. A suspended position is tied to the exact uncertain
tool continuation that produced the current state. This is logical preservation;
it does not establish durable writes, truthful operator assertions or external
success. Mixed approval provenance also treats a tool intent as consuming the
grant when its completion is lost; recovery cannot restore permission to repeat
the operation. Shared [record-frame facts](../Harness/Proofs/RecordFrames.lean)
connect these arguments to the executable record decoder.

The [source/axiom audit](../scripts/check_core.py) rejects proof placeholders,
unauthorized axioms, runtime imports and unsafe substitutions in the verified
core. Theorem counts are an audit manifest, not a count of independent product
guarantees. Lean's kernel and allowed axioms support proof checking; compiler and
runtime correctness remain execution assumptions.

## Runtime evidence

| Boundary | Checks |
| --- | --- |
| Pure protocol | [900 Plausible cases](../Tests/Properties.lean), deterministic core/provider/compaction fixtures, and typed recovery tests. |
| Response repair | [Executable scenarios](../Tests/ResponseRepair.lean) check rejected batches, truncation, malformed replies, usage, cancellation and replay. [CLI tests](../Tests/integration.py) interrupt at a durable boundary and verify that correction can continue while the repair ceiling remains spent. |
| Request budget notice | [Budget-context tests](../Tests/BudgetContext.lean) check remaining allowances after reservations, retry/summary accounting, exact context-byte admission and replay. The notice remains outside raw history and summary source material. |
| Stateful real IO | [Generated operation sequences](../Tests/RuntimeProperties.lean) compare real files and journals with an independent small model. Default: 200 × 30 operations, plus 100 generated-data cases. Extended: 2,000 × 100 operations. Failures report seeds and use fresh fixtures for deletion shrinking. |
| Linked recovery | [40 × 12 generated turns](../Tests/RecoveryProperties.lean) combine real reads/edits and journal reopening with injected lost observations and operator resolution. A separate model checks cumulative calls, usage, repair limits, identities, result order and file effects. Duplicate administrative records must fail; shrinking reruns each candidate from a fresh fixture. |
| HTTP and streaming | [Transport](../Tests/provider_transport.py) and [streaming](../Tests/provider_streaming.py) tests use local servers and the compiled adapter: split Unicode/events, deadlines, cancellation, incomplete bodies, stop/usage validation and credential suppression. Server barriers test both completion-before-cancellation and cancellation-before-completion. |
| JSON admission and persistence | [Numeric resource tests](../Tests/provider_json_bounds.py) exercise compiled parsing under process limits, including aggregate numeric work and tool arguments inside streamed events. [Journal tests](../Tests/journal_serialization.py) reject values that the pinned JSON printer/parser cannot round-trip without changing the JSON value. Refusal preserves the durable prefix and prevents unrecorded advancement. |
| Process isolation | [Sandbox contracts](../Tests/sandbox_contracts.py) check the actual bubblewrap profile, absent host data/network/descriptors, canonical workspace aliases, mount collisions, exit status and detached-child cleanup. |
| Settled timeouts | [Timeout contracts](../Tests/process_timeouts.py) check detached-child cleanup, cancellation and deadline ordering, status/cleanup failures, skipped calls, model continuation and crashes before/after durable completion. |
| Artifact integrity | [Artifact contracts](../Tests/artifacts.py) check ranged binary retrieval across reopened processes, corruption, symlink/hardlink substitution, quotas, orphan bytes and failed writes/flushes. |
| Approval and output | [Event tests](../Tests/event_output.py) cover slow pipes/terminals, bounded queues, explicit delivery failure and unambiguous escaped approval arguments. |
| Crash recovery | [Crash tests](../Tests/crash_recovery.py), [lost-operation tests](../Tests/recovery_observations.py) and [session boundaries](../Tests/session_boundaries.py) count effects around intent/completion/resolution boundaries, failed synchronization, locks and session copying. |
| Durable follow-ups | [Combined CLI tests](../Tests/DurableSessions.lean) run both applications through three turns, five compactions, restart and a lost reply after a committed mutation. They check cancellation settlement, turn-scoped markers, failed follow-up writes, cumulative accounting and inspect/replay agreement. |
| Scoped permission boundaries | [CLI cases](../Tests/capability_policy.py) exercise recursive reads, edit preparation, exact command arguments, strict policy files, inventory rights and frozen restrictions. [Generated cases](../Tests/Capabilities.lean) cover component matching and policy encoding. |
| Retained journal writer | [Writer contracts](../Tests/JournalWriter.lean) use real writes and a Rust fault shim to test torn records, failed file/directory synchronization, crashes, poisoned handles and reopening. A read-denial case checks that later appends do not reread the prefix. |
| Native ABI | [ABI tests](../Tests/native_abi.py) repeatedly cross the real Lean/Rust boundary with borrowed/binary/Unicode values, boxed integers and descriptor ownership. They do not prove unsafe-code memory safety. |
| Storage capacity | [Adapter measurement](../Tests/journal_scale.py) and [whole-session measurement](../Tests/session_capacity.py) exercise the 64 MiB journal ceiling. The latter also fills the artifact quota, retrieves a diagnostic beyond the display prefix and checks logical replay after storage refusal. Both use synthetic data. |

These are selected fault cases and generated sequences, not exhaustive concurrent
interleavings or simulated power loss. [CI](../.github/workflows/ci.yml) runs the
standard gates and schedules the larger generated IO run weekly. Live evaluations
measure task correctness, interventions, usage and recovery separately in
[eval/](../eval/README.md).

The current [durable-session gate](reports/2026-11-11-durable-sessions.json) passed
the full Lean build, executable and generated tests, 156 Python adapter checks,
five JSON codec checks and the 184-name source/axiom audit. Both installed
applications pass the combined follow-up/recovery gate. These checks use scripted
or local fake providers; they do not measure live task quality.

The previous [adapter gate](reports/2026-11-09-adapter-checks-v6.json) passed 156
checks plus five independent JSON codec checks, with no skips. The rebuilt
candidate also passed the 130-name source/axiom audit, 900 generated core cases
and default generated IO suites. New cases cover settled sandbox timeouts,
skipped calls, durable continuation and deadlines across request preparation.
The same delayed-preparation fixture caused late tool and HTTP dispatch on the
preserved earlier binaries and prevented both on the corrected binaries.
An independent evaluator reconstructed all three requests in the retained
timeout/inspection CLI trace.
The earlier [schema-4 gate](reports/2026-11-09-adapter-checks-v4.json) remains retained. Three earlier sandbox
failures remain unexplained; two saved observations
show cleanup timeouts, while the first lacks its full error. A
[reassessment](reports/2026-11-09-cleanup-reassessment.json) passed 180 invocations
of those exact cases on the schema-4 candidate without reproducing a timeout.
The separately fixed Linux dead-process parser defect follows a different error
path. These passes do not establish the cause of the earlier failures.

The [extended local run](reports/2026-11-09-extended-io-v2.json) passed 2,000 × 100
filesystem operations and the default recovery sequences in 252 seconds. It used
the November 9 candidate on a shared host; hosted weekly CI timing remains separate.

A [live artifact trial](reports/2026-11-09-artifact-live.json) retrieved a failed
check's log tail, repaired the code and passed 1,681 independent cases. It took
seven model calls and cost $0.156556. The prior fixture setup failure is retained;
both attempts cost $0.166252. This tests the retrieval mechanism on a small
self-authored task.

The historical [capacity run](reports/2026-11-09-session-capacity-v4.json) retained a
63.7 MiB journal and 64 MiB of artifacts across 58 scripted model requests on the
schema 5 binary. The test passed by observing the expected storage-refusal exit 2;
no terminal outcome could be saved. Inspect and replay succeeded, and the 59th
reserved model attempt was never dispatched. Artifact retrieval beyond the
display limit and a zero-retained marker at quota exhaustion were checked.
Execution took 525 seconds and replay 2.07 seconds. Maximum worker RSS was
661 MiB during execution and 417 MiB during replay, not total process-tree memory.
That implementation reread the journal on append; late request intervals reached 16.6 seconds,
including intervening operations. This exposes a sustained-session performance
limit, not isolated append latency or evidence of live task quality. The current
runner validates the prefix once per open and retains its append cursor. The
[writer benchmark](reports/2026-11-11-journal-writer.json) measures this separately;
reopening still validates the complete bounded journal.

The current [whole-session capacity run](reports/2026-11-11-session-capacity.json)
reached the same 64 MiB journal and artifact ceilings after 58 scripted model
requests. Execution took 40.2 seconds with 303 MiB peak per-process RSS. A read's intent
fit but its completion did not; the CLI stopped with exit 2 and retained that
operation as unresolved. Inspect and replay agreed, taking 4.3 and 4.2 seconds;
their peaks were 580 and 563 MiB. No terminal outcome could be saved. These are
single synthetic runs on a shared host, not controlled performance comparisons
or measurements of total process-tree memory. GNU time includes the command and
waited-for children in its per-process maximum. The first attempt exposed an old
fixture assumption about which record would exhaust the quota; its failure is
retained alongside the corrected check.

## Assumptions and limits

- **Filesystem:** direct edits assume a single workspace writer. Descriptor-relative
  access rejects traversal, but preimage hashing is not an atomic compare-and-swap.
  Durability assumes persistent local storage honoring file and directory `fsync`.
- **Host profile:** an approved command has the user's OS privileges. A working
  directory or filtered environment does not isolate credentials or session files.
- **Bubblewrap profile:** tool processes receive only the fixed declared mounts,
  private home/temp and namespaces. Operator-supplied read-only installation trees
  must contain no secrets. Startup scans reject known unsafe workspace objects;
  later execution assumes settled prior tools and no concurrent external writer.
  Timeout settlement also assumes the fixed reviewed namespace-init process graph,
  Linux namespace teardown and complete procfs visibility of owned processes in
  the caller's PID namespace. Failed checks retain uncertainty.
  This is a tested Linux profile, without multi-tenant or resource-quota claims.
- **External effects:** cancellation may leave changes behind. A local journal
  cannot make arbitrary shell commands or remote requests exactly-once. Unknown
  effects are preserved and uncertain mutations are never blindly repeated.
- **Recovery assertions:** a matching edit postimage establishes observed desired
  contents after synchronization. Process resolution depends on the operator's
  assertion that original resources are settled. Neither is an independent proof
  of the operation's history or correctness.
- **Provider:** lost responses may incur cost. Missing usage remains unknown;
  call/output limits do not establish an exact token or dollar ceiling. Complete
  streamed content must pass validation before becoming authoritative.
- **JSON library:** provider and journal input passes a lexical resource check
  before Lean's parser: at most 4,096 numeric digits, exponent magnitude 4,096,
  depth 128 and 1,048,576 units of decimal-digit work. Streaming events and their tool
  argument reparses share the work allowance. These are admission rules, not a
  proved memory or time bound. Journal writes also require a successful round-trip
  under Lean's JSON value equality; this does not prove every typed reply codec.
- **Compatibility:** schema-7 resume requires the same executable, installed application identity and frozen
  configuration. Older sessions retain their original binary. No automatic
  schema migration, snapshot acceleration or damaged-tail repair is implemented.

The [runtime reference](../runtime/README.md) specifies profile setup, output
limits, context admission and each recovery disposition. The November 9
[product-only build](reports/2026-11-09-clean-install-v4.json), using cached
dependencies, reproduced its four schema-5 binaries and passed a sandboxed
read/edit/check workflow without Python on its execution path. That measurement
concerns schema 5. The current schema-7 evidence is in the
[durable-session validation](reports/2026-11-11-durable-sessions.md) and
[live task report](../eval/reports/2026-11-11-durable-sessions.md).

## Motivating failures

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

## Application boundary

The execution core, typed effects and journal replay are parameterized by a compiled-in
application. Coding remains the source of the historical live evaluation evidence above.
Inventory exercises the same machinery with different operation/result types, frozen
starting data and a session-local reservation ledger; its tests do not constitute a live task-quality comparison. Schema-5 evidence
is retained for its original binary and is not relabeled as a schema-7 measurement.

Application code supplies permission classification, codecs and recovery rules. The core
controls IDs, grants, reservations and state transitions. Only trusted startup selects an
application; resume validates its ID/version and the executable identity. These contracts
do not make a new application's IO safe merely because its types compile.

Inventory reservations test a second mutation domain: a process exits after the ledger
commits but before the harness saves a completion. Recovery must use the matching receipt
without another stock debit. The ledger assumes trusted session storage and cooperating
writers using its lock. Checksums detect damaged records; they do not authenticate them.
This is a local application example, not a claim about transactions in an external warehouse
service. See the [application guide](Applications.md#recovering-a-committed-reservation).
