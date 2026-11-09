# Flask budget diagnostic

This follow-up compared the Lean harness and Pi again on Flask's blueprint task from SWE-bench Lite, using its official evaluator. It was selected after both engines failed both original runs and is **excluded from the frozen comparison**. The binaries, task, and product prompts stayed unchanged; neither model received hidden-test findings.

Each engine received two new runs with **24 provider attempts and 48 tools**, doubled from 12 and 24. The 300-second agent allowance and 4096-token output ceiling stayed unchanged.

| Engine | Run | Official result | Finished normally | Model calls | Cost |
| --- | --- | --- | --- | --- | --- |
| Lean | 1 | Fail | Yes | 17 | $0.974812 |
| Lean | 2 | Fail | Yes | 15 | $0.813180 |
| Pi | 1 | Fail | Yes | 10 | $0.288392 |
| Pi | 2 | Pass | Yes | 15 | $0.575764 |

Finished normally means exit code 0, not a correct patch. Both Lean runs finished but failed the official check: extra calls alone did not resolve this task. Pi passed once and failed once. These selected repeats do not establish a general budget effect or a harness correctness fix.

Total: **1/4 official passes**, 4 normal finishes, **$2.652148** accounted cost, and 0 unknown-usage requests.

The original comparison's limits still apply: Lean uses a 120,000-byte context estimator, Pi its native policy, and both a 144,000-byte broker request ceiling. Only Lean received the extra no-test-edit instruction, so the stored stricter success flag is not comparable. Elapsed time includes setup and excludes grading; memory was unmeasured.

[Run JSON](2026-11-09-flask-budget-diagnostic.json) retains calls, failures, costs, and binary hashes. The [original public report](2026-11-09-public-sample.md) preserves the earlier results and setup failures.
