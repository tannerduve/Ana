# Four-repository development calibration

We compared the Lean harness with Pi 1.5.0 using `claude-opus-5-5` on four
preselected development issues in pytest, Pylint, Sphinx and SymPy, with the
pinned SWE-bench Lite evaluator.
This is a selected sample, not the full benchmark or a held-out comparison.
Both engines passed the official checks and finished normally on all four tasks.
All eight failed the original, stricter qualification because an existing test
file changed. These are separate findings; a normal finish alone does not mean
that a patch passes its checks.

| Task | Lean: calls / cost | Pi: calls / cost | Official checks | Normal finishes | Original qualification |
| --- | ---: | ---: | ---: | ---: | ---: |
| pytest #5227 | 28 / $1.820296 | 10 / $0.336672 | 2/2 | 2/2 | 0/2 |
| Pylint #7114 | 27 / $1.760548 | 19 / $1.597296 | 2/2 | 2/2 | 0/2 |
| Sphinx #8721 | 13 / $0.680404 | 13 / $0.408488 | 2/2 | 2/2 | 0/2 |
| SymPy #18189 | 8 / $0.187516 | 11 / $0.307992 | 2/2 | 2/2 | 0/2 |
| **Total** | **76 / $4.448764** | **53 / $2.650448** | **8/8** | **8/8** | **0/8** |

Calls include summaries. All 129 provider requests settled with known usage;
total cost was **$7.099212** against the $12 development allocation. There were
no unrun slots, extra attempts, infrastructure failures or output-truncation
stops. Lean accepted two summaries, one each in pytest and Pylint. No run had a
scheduled restart, so this cohort does not establish sustained-session readiness.

## What the test-file qualification means

The shared instruction said “Preserve existing tests, assertions, and theorem
statements” and “You may add regression tests.” The frozen grader instead
required detected existing test files to remain byte-for-byte unchanged.
Six patches only added regression tests to existing files. The two pytest
patches also adjusted expected logging-format patterns for the requested
behavior. The file rule therefore rejects permitted additions; it is not
evidence that all eight patches violated instructions or bypassed checks.
Lean also received the conflicting system instruction “Do not modify existing
tests”; the engines' instructions were not fully aligned.
Original scores remain **0/8**. Any revised rule applies only to a future cohort.

The official evaluator replaced these affected test files with its pinned test
versions before grading. Its eight passing results therefore did not depend on
the candidate-added assertions. This does not prove that every possible checker
bypass is excluded. Exact paths, instruction text and hashes are in the
[original summary](2026-11-09-development-v2.json).

## Audit and scope limits

Two original Lean session audits failed because the independent auditor encoded
tabs differently from pinned Lean. A separately versioned
[diagnostic](2026-11-09-development-v2-audit-diagnostic.json) passes all four
session audits without changing journals, patches or original verdicts.

This product comparison used 40 model attempts, 120 tools, 4,096 output tokens
and 900 seconds per run. Lean used a 120,000-byte context allowance and 90-second
tool deadlines; Pi retained native context and tool timeout policies. Lean used
provider-default effort, Pi low effort, and their tool isolation differed.
Shared-host timing included concurrent validation; sampled container memory
includes page cache and is not process RSS.

Results belong to CLI `bf2b090d`, not the later JSON-hardening revision. Three
earlier cleanup timeouts remain unexplained. A separate numeric-serialization
fault was found after this freeze; no numeric-serialization corruption or replay
failure was observed in this cohort.
Four tasks provide development evidence, not statistical parity or a guarantee
that the next workload fits the budget.
