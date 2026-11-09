# First implementation validation — 2026-11-08

This is development evidence, not a held-out task evaluation or a Pi comparison.

Environment: Linux x86_64, Python 3.12.3, Lean 4.33.1, Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Python uses its standard library. Local commands run from the project root.

| Evidence | Result |
| --- | --- |
| `lake build` | Passed: library, CLI, executable test suite and proofs compile |
| `lake exe harness_tests` | Passed: 28 core checks, 19 provider checks, replay/serialization suite |
| `python3 scripts/check_core.py` | Passed: core source/import guard and 8 selected theorem axiom audits |
| `python3 -m unittest discover -s runtime -p 'test_*.py' -v` | 18 passed |
| `python3 Tests/integration.py` | 11 passed |
| Live provider repository task | Not run: no `ANTHROPIC_API_KEY` in environment |
| Pi baseline and repeated held-out tasks | Not run |

The CLI integration scenario reads a Python program, changes subtraction to addition using an exact preimage-checked edit, runs a real Python regression command, and reaches a final model response. The model messages in this scenario are scripted; they do not demonstrate model task-solving quality. The final file and command output are checked independently by the test driver.

Recovery tests reconstruct a session after a durable tool completion and verify that the completed mutation is not repeated. A separate test removes that completion, leaves its intent, and confirms that resume refuses to execute it. Tests also cover single-writer locking, interrupted final storage, batch rejection, truncated model output, denied commands, call/context limits, active-process cancellation, real PTY approvals, symlink/preimage rejection, fake HTTP, and injected storage failures.

Kernel checking establishes budget preservation over reachable states, emitted-tool authorization, rejection of changed approval grants, and the stated terminal/cancellation properties. Replay determinism has a proof; correspondence between recorded JSON and reconstructed states is currently tested. The full history/correlation invariant is not yet proved. All audited theorem dependencies are within `propext`, `Classical.choice`, and `Quot.sound`; no proof placeholders or additional project axioms are permitted by the check.

Not measured: independent live task success, human intervention rates, real provider latency/cost, unknown-usage incidence in production, peak memory, long-session quality, compaction, or parity with another harness. These results support the first implementation only. The README lists remaining release gates and runtime assumptions.
