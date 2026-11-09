# Durable sessions: implementation and local validation

November 11, 2026. The runtime now accepts follow-up tasks, executes a proved
persistence protocol, and keeps a validated journal cursor while a session is
open. Both applications have proved operation, result and rendering contracts.

## What changed

| Change | Guarantee and boundary |
| --- | --- |
| `continue SESSION --task TEXT` | A new turn retains configuration, spent budgets, history and operation identities. Old grants cannot authorize it. Unresolved effects block continuation. |
| Executable persistence protocol | Dispatch requires the matching intent acknowledgment; advancing the core requires the completion acknowledgment. Storage failure stops the protocol. The adapter still supplies the meaning of a successful durable write. |
| Application laws | Coding and inventory establish valid decoding, round trips for valid values, and faithful conversion of observations into model-visible results. These do not establish that an external observation is true. |
| Retained journal writer | Validate the prefix once under the session lock, then maintain its sequence, checksum and size. An uncertain append poisons the cursor until reopening. |
| Cancellation settlement | Undispatched calls receive ordered not-executed results. A dispatched operation with an uncertain outcome still requires recovery. Cancellation markers belong to individual turns. |

Session schema 7 requires the identical executable, installed application
ID/version and frozen configuration. No automatic migration from older sessions
is provided.

## Combined CLI gate

The [test](../../Tests/DurableSessions.lean) runs real CLI processes with scripted
model replies and real storage faults.

| Check | Coding | Inventory |
| --- | --- | --- |
| User turns / accepted compactions | 3 / 5 | 3 / 5 |
| Actual process restart | Pass | Pass |
| Mutation committed before reply loss | File edit | Stock reservation |
| Recovery without repeating the mutation | Pass | Pass |
| Unresolved effect blocks follow-up | Pass | Pass |
| Cancellation settlement and retained budgets | Pass | Pass |
| Final inspection agrees with replay | Pass | Pass |

The full Lean build, six executable gates, 161 boundary checks and three Rust
unit tests passed. Source-boundary and selected axiom audits passed. The
[validation record](2026-11-11-durable-sessions.json) binds the sources, executable,
test sources and logs. These tests use no live provider calls; task quality is
reported separately in the [evaluation workspace](../../eval/README.md).

## Journal performance

One local synthetic measurement took 16 append samples at each size. Each
sample writes about 1 KiB and includes file and directory synchronization.

| Existing journal | Median retained append | Sampled resident memory |
| --- | ---: | ---: |
| 1 MiB | 0.595 ms | 108 MiB |
| 16 MiB | 0.555 ms | 111 MiB |
| 60 MiB | 0.702 ms | 111 MiB |

Reopening and validating the 60 MiB prefix took 1.760 s. The compatibility
one-shot append, which revalidates on each call, took 1.48–1.73 s. This measures
the benefit of retaining the cursor on this host; it is not a hosted latency
guarantee. The whole benchmark peaked at 897 MiB during prefix revalidation and
quota-fixture construction, outside the retained-append samples.
[Measurements and faults](2026-11-11-journal-writer.json).

A separate [CLI capacity test](2026-11-11-session-capacity.json) reached the
64 MiB journal and artifact allowances after 58 model requests and 61 tool
dispatches. A read's completion no longer fit. The CLI reported storage failure,
kept its intent pending and did not report a saved terminal outcome. Inspection
and replay agreed; they took 4.32 s and 4.22 s, with peak RSS of 580 MiB and
563 MiB respectively. The running session peaked at 303 MiB. These are GNU
`time` per-process maxima, including waited-for children, not simultaneous
process-tree memory.

Full-prefix reopen remains a scaling cost. The tests cover process crashes and
injected syscall failures; they do not simulate power loss. Physical durability
requires persistent storage honoring the documented synchronization contract.
