# Rust bindings validation — November 9, 2026

The Lean executable with direct Rust bindings completed the parser-repair task
through the real Anthropic API. The core and proofs were unchanged. Rust supplies
the native file, process, signal, and crypto primitives; Lean still runs the
agent and IO logic. There is no handwritten C wrapper or Python runtime.

| Measurement | Result |
| --- | --- |
| Model | `claude-opus-5-5` |
| Independent checker | 43 cases passed; clean baseline failed |
| Existing fixture tests and README | Unchanged |
| Elapsed task time | 19.660 seconds |
| Model attempts / tool dispatches | 5 / 7 |
| Reported input / output tokens | 17,806 / 2,107 |
| Unknown-usage observations | 0 |
| Saved-session inspection | Passed |
| Watchdog termination | None |

The executable SHA-256 was
`c0375ab63b39279c7198c46628b9d2a51da225dd5afa8a9c990a9d5e951e39dd`.
The [recorded measurements](2026-11-09-rust-native.json) include hashes of the
native sources, build inputs, fixture, and checker. The run used the uncommitted
migration before the repository history was squashed; its recorded HEAD is the
previous revision, not the tested source identity. The executable and source
hashes identify what ran. Raw sessions and credentials are not published.

The reviewed patch changes only `ranges.py`: it validates positive ASCII
integers, includes both range endpoints, rejects malformed or descending ranges,
and returns sorted unique values. The checker runs separately from the agent;
see [the evaluation setup](../../eval/README.md).

Validation also passed:

- The full Lean build, deterministic core/provider/recovery fixtures, and selected
  15-theorem axiom audit.
- 900 Plausible-generated protocol cases and 100 real-filesystem/journal cases.
- 64 external tests covering native ABI values, HTTP, processes, files, session
  boundaries, and injected crashes. The three ABI tests repeat sensitive calls
  10,000 times and check descriptor counts and independent value oracles.
- Rust formatting, Clippy with warnings denied, and the native unit test.

This is one development task after changing the native bindings. It does not
measure general reliability or establish memory safety. Compaction, uncertain-edit
reconciliation, and OS sandboxing remain unimplemented.
