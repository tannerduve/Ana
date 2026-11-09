# Evaluation workspace

The benchmark runners, pinned Pi baseline, fixtures and recorded results live in
this directory of the main repository. They have their own build and tests and
are not required to build or run the product.

The [November 11 durable-session evaluation](reports/2026-11-11-durable-sessions.md)
completed all 16 planned runs on four known repository features. Independent
review qualified **8/12 Lean runs** after a documented evaluator correction.
All four capped Pi runs stopped early; this cohort does not establish relative
harness quality. Reported usage cost **$22.596516** at the configured token prices.

The report separates task correctness, normal completion, replay, summary
fidelity and evaluator defects. It includes a reproduced counting bug missed by
the Pylint checker and reference patch, plus a correction to an earlier assumption
about Pi's reasoning settings. These are development results, not held-out
evidence or a production-readiness claim. The 72-run held-out comparison remains
unrun.

| Earlier report | What it established |
| --- | --- |
| [Local comparison](reports/2026-11-09-comparison.md) | 61/64 Lean and 63/64 Pi runs finished normally with checker-passing code on a small known corpus. |
| [Two-run follow-up](reports/2026-11-09-calibration-followup.md) | Both known tasks qualified; Sphinx passed its continuation gate. Predates outbound-request digests. |
| [Four-run calibration](reports/2026-11-09-calibration.md) | Two patches passed checks; none qualified because all four runs ended abnormally. |
| [Sustained v4](reports/2026-11-09-sustained-v4.md) | 12/16 runs started; 11 checker passes, one original qualification and two under separate corrected reanalysis. The gate failed. |
| [Sustained v3](reports/2026-11-09-sustained-v3.md) | Earlier trial and launcher failure, retained separately. |

See the [comparison protocol](PROTOCOL.md) and [public benchmark setup](PUBLIC.md)
for reproducible commands and the limits of each track.

## Setup

Use Linux with Python 3.12+, Node 24.16.0, bubblewrap, GNU `time`, elan, rustup,
OpenSSL development files and a C compiler/linker. Docker and pinned upstream
assets are additional requirements for public benchmarks. Lean and Rust pins
match the enclosing product package. Select a dedicated Node distribution with
`NODE_BIN=/absolute/node-distribution/bin/node`; system prefixes such as `/usr`
are rejected as portable mounts. New frozen campaigns bind its executable path,
SHA-256, version, and distribution root. The coordinator carries that approved
selection through its sanitized environment; Pi startup is checked in each exact
task image before a provider endpoint is admitted.

From the repository root:

```sh
lake build
cd eval
lake build
npm ci --prefix baseline --ignore-scripts
```

The evaluation Lake package depends explicitly on `..`. Its `eval_tools` proxy
imports the product's actual tool implementations; it contains no agent loop.
Product sources are not copied into this package. The regular product build
excludes this target and all Node/Pi dependencies.

Runners default to the enclosing product. `--harness-root PATH` or
`LEAN_HARNESS_ROOT` selects a deliberate alternative, which must match the proxy's
build identity. Admission checks product build freshness without rebuilding,
source fingerprints, compiler versions and executable hashes before paid work.
See [development notes](DEVELOPMENT.md) for cache reuse and overrides.

## Offline checks

Run from `eval/`:

```sh
python3 Tests/evaluation.py
python3 Tests/campaign.py
python3 Tests/path_configuration.py
python3 Tests/broker_responses.py
python3 Tests/broker_requests.py
python3 Tests/evaluation_baseline.py
python3 Tests/evaluation_isolation.py
python3 Tests/continuation_audit.py
python3 Tests/evaluation_patches.py
python3 Tests/evaluation_window.py
python3 Tests/public_reporting.py
python3 Tests/public_preparation.py
python3 Tests/session_audit.py
python3 Tests/workspace_snapshot.py
python3 Tests/sustained.py
python3 corpus/test_checkers.py
python3 corpus/validate.py --output /tmp/corpus-validation.json
```

These use local fixtures and fake HTTP servers. The Pi adapter check needs the
built proxy and installed packages. `Tests/public_coq_audit.py` additionally
requires its already-cached pinned image; it does not download one implicitly.
The separate evaluation CI job covers offline machinery and fixture isolation;
product/proxy integration is also an explicit local gate.

[Live commands](PROTOCOL.md) require the [shared spending ledger](ACCOUNTING.md).
For the current harness, select `--task-context-version 4` in `suite.py`,
`public_bench.py run`, and `sustained.py run` before execution. This records the
request format for auditing; it does not change the harness's behavior. The CLI
default remains 1 for historical compatibility. Preserve recorded plan versions.
Schema 7 audits bind the coding application/version and the exact proxy-exported
schemas (`tool_schemas_sha256`), including schemas in request byte accounting.
Schema 6 remains unsupported; schemas 2–5 retain their historical interpretation.
Unattended plans declare no follow-ups. The auditor accepts `user_turn` records
only when the plan explicitly lists their exact texts in `user_turns`; it checks
consecutive turn/operation identities and cumulative budgets without resets.
These declared turns are reported separately, not treated as unattended success.
Recovery/resolution interventions still fail the unattended audit. Compiled replay
checks typed application decoding and policy; the independent audit checks recorded
history, contexts, counts, events, artifacts and provider evidence.
Keep API keys, raw sessions and run directories outside Git. The small recorded
schema-7 test fixtures contain only scripted local data and synthetic zero-cost
accounting, with capture/source/binary identities; they make no provider claim. Historical fixture, checker,
lock and report data are preserved; [extraction.json](extraction.json) records the
earlier temporary extraction and original source identities. New plans record
both product and evaluation source hashes even though they share one Git history.
