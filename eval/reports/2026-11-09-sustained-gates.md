# Sustained-session deterministic gates — November 9, 2026

The schema-2 implementation passed the deterministic compaction, restart and
recovery gates below. These tests use scripted model responses or local fake
HTTP servers. They make no live task-quality, summary-fidelity or Pi-parity claim.

Tested production executable SHA-256:
`69b48cdce05cd3a9bc8fd64e6e1d5dd1bace6b50cf4f5f65e8c290fc384f3fcb`.
The build uses Lean 4.33.1 and Rust 1.97.1 with direct native bindings. Session
and state schemas are version 2; the journal frame format remains version 1.
Resume requires the identical executable and does not migrate older sessions.

| Gate | Result and scope |
| --- | --- |
| Lean build and deterministic fixtures | Passed, including core, recovery, compaction and 29 provider contract checks. Summary encoding omits tools and preserves instructions. |
| [Core source and axiom audit](https://github.com/tannerduve/lean-harness/blob/fd7f6cb38cf62ec147186dfec540e32eaeb00c34/scripts/check_core.py) | Passed for 24 selected theorem reports. The allowed axiom set is `propext`, `Quot.sound`, `Classical.choice`; source checks reject the listed placeholders, unsafe substitutions and runtime imports. |
| [Pure generated properties](https://github.com/tannerduve/lean-harness/blob/fd7f6cb38cf62ec147186dfec540e32eaeb00c34/Tests/Properties.lean) | 900 Plausible-generated provider/core cases passed, using seeds 41001–41003 and shrinking. |
| [Generated real IO properties](https://github.com/tannerduve/lean-harness/blob/fd7f6cb38cf62ec147186dfec540e32eaeb00c34/Tests/RuntimeProperties.lean) | 100 filesystem/journal cases passed, seeds 52000–52099, plus the ASCII-search contract. Inputs are generated; operation sequences are fixed and this suite does not shrink. Together the two suites account for 1,000 generated cases. |
| [CLI integration](https://github.com/tannerduve/lean-harness/blob/fd7f6cb38cf62ec147186dfec540e32eaeb00c34/Tests/integration.py) | 17 tests passed, including compaction/restart, scheduling yields, frozen loopback configuration, external-endpoint rejection and recovery of a recorded interruption with remaining calls. |
| [Crash and recovery](https://github.com/tannerduve/lean-harness/blob/fd7f6cb38cf62ec147186dfec540e32eaeb00c34/Tests/crash_recovery.py) | 10 tests passed, with parameterized fault cases. They cover intent/completion boundaries, edit postimages, conflicts, operator resolutions, resolution persistence and failed reconciliation fsyncs. These are not ten distinct crash locations or exhaustive fault coverage. |

The compaction/restart fixture performs two reads, installs one summary, and
yields after 12 durable completions. Its limits are `maxContextBytes=26000`,
`compactAtPercent=85`, `compactionKeepMessages=2`, and `maxSummaryBytes=2000`.
At exit 75 it has no pending intent or terminal record, three model attempts
(including the summary), two tool reservations, and five unchanged raw messages.
Resume reaches the scripted final answer with four model attempts and the same
two tool reservations. The accepted summary and raw prefix survive unchanged;
offline replay reconstructs the same final inspection state. This checks
continuation mechanics, not whether a model writes a useful summary.

Recovery checks distinguish matching postimages, unchanged preimages and
conflicts. A postimage is rechecked and the file and directory are synchronized
before the resolution record is persisted. Injected sync failures leave the
intent unresolved. Failures before a resolution write and a crash after its
durable flush preserve replay behavior without another edit reservation.

Process resolution records an explicit operator assertion for the exact
operation ID. Tests reject a duplicate resolution and a note masquerading as
the required `--resources-settled` flag. Completion and abandonment never rerun
the original command; recorded interruptions retain the remaining batch and
its counters. Operator assertions do not independently verify command success
or physical cleanup.

The compaction proofs cover preserved raw history and instructions, admitted
summary requests, shared attempt reservations, accepted response structure and
bounded paired active context. Replay's theorem remains a determinism claim.
Durable writes, filesystem behavior, native memory safety, summary fidelity,
and successful task completion remain outside those proofs. Broader recovery,
hostile-filesystem races, automatic storage repair and process containment still
need further work; see [Safety.md](https://github.com/tannerduve/lean-harness/blob/fd7f6cb38cf62ec147186dfec540e32eaeb00c34/docs/Safety.md).

Reproduce the reported gates from the repository root:

```sh
lake build
lake exe harness_tests
lake exe runtime_properties
python3 Tests/integration.py
python3 Tests/crash_recovery.py
python3 scripts/check_core.py
```
