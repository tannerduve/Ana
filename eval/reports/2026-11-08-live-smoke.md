# First live coding task — November 8, 2026

**Passed: one real Anthropic Opus 5.5 run repaired a parser and passed 43 independent checks.** This is a self-authored development task, not a held-out evaluation or evidence of parity with Pi.

The unmodified Lean harness called the Anthropic Messages API directly. There were no scripted responses, manually supplied tool calls, or human edits to the candidate. The model inspected the fixture, edited `ranges.py` using the preimage-checked edit tool, ran the existing tests and its own additional checks, and returned a final explanation.

| Measurement | Result |
| --- | --- |
| Configured model | `claude-opus-5-5` |
| Harness result | Final answer, exit 0 |
| Independent checker | 43/43 cases passed |
| Seeded baseline | 24/43 cases failed |
| Existing tests | 4 passed; test file and specification unchanged |
| Elapsed harness run | 24.622 seconds |
| Model attempts | 5 |
| Tool dispatches | 7: list ×1, read ×3, edit ×1, process ×2 |
| Known input/output tokens | 18,565 / 2,032 |
| Unknown-usage observations | 0 |
| Human intervention during task | None |

The [task](../tasks/ranges/README.md) requires positive ASCII integers and inclusive ascending ranges, whitespace handling, sorted unique results, and rejection of malformed input. The [checker](../tasks/ranges_check.py) tested the final file independently; the model could not see or edit it during its run. The checked source SHA256 is recorded in the [metrics](2026-11-08-live-smoke.json), alongside the executable, helper, checker, and fixture hashes. The [resulting patch](2026-11-08-live-smoke.patch) changes only `ranges.py`.

The harness source was at commit `9e3ff64ba63d87fb4f689709f26cd929f5dc8261`. The evaluation driver, fixture, and checker were new uncommitted files during this run and are included with this report. The reporting script subsequently gained source hashes; the executed harness binary and helper were unchanged. Private raw session evidence was retained locally; credentials and raw transcripts are not included in the report.

The driver used bubblewrap to expose a disposable workspace, session directory, executable/helper, config, and system runtime. Host home and the checker were absent from the model environment. Network access and `/proc` were shared within that environment; this was not a hostile-code or credential-isolation test. The external checker ran afterward without an API credential. See [evaluation instructions](../README.md) to reproduce the setup.

This result establishes the live model→tool→model path and a correct final artifact for one small task. It does not establish long-session reliability, compaction quality, crash recovery under live workloads, cost efficiency, or performance on a broader task distribution. The model's final explanation was not separately scored.
