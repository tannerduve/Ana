# Evaluation

Read the [November 9 results](reports/2026-11-09-comparison.md) for what ran and
what passed. This directory contains the corpus, runners and checks needed to
repeat the experiments. “Lean” below means this harness running a model; the
corpus includes several programming languages.

## Local comparison protocol

The [manifest](corpus/manifest.json) fixes 16 self-authored tasks: 12 development
and four reserved from prompt/tool tuning. Each run starts with a fresh fixture.
Before paid execution, every baseline must fail and every reference must pass
its independent checker. Reserved tasks are not claimed to be absent from model
training.

| Track | Configuration |
| --- | --- |
| Controlled | Pi agent-core and Lean share Lean tools, schemas, instructions, sequential scheduling and a byte-based context estimator. Compaction and retries are disabled; Pi reasoning fields are removed from requests. The loops and history handling still differ. |
| Product | Pi's coding-agent SDK and Lean use their respective tools, prompts and context policies under shared limits and zero retries. Pi extensions, skills and ambient context files are disabled. Reasoning controls differ; inference effort is not matched. |

Defaults: `claude-opus-5-5`, 12 provider attempts, 40 tools, 4,096 output tokens,
120,000 estimated context bytes, 90 seconds per operation and 300 seconds per run.
Product context policies differ; both also face a broker request-byte ceiling.
The full schedule is **16 tasks × 2 engines × 2 tracks × 2 repetitions = 128 runs**.

Pi **1.5.0** and its dependencies are [locked](baseline/package-lock.json).
Node/Pi are evaluation dependencies, not production harness dependencies.

A November 11 local encoding probe corrected the earlier claim that this Pi
configuration simply requests low effort: the pinned adapter emits adaptive
thinking, a low top-level effort and a high effort in its final system message.
The probe checks request construction, not provider interpretation or historical
body equality. New broker records retain bounded settings evidence; older records
have body hashes and lengths without those fields.
[Evidence and comparison limits](reports/2026-11-11-durable-sessions.md).

For a separately frozen sustained **product** cohort, a Pi mode can optionally
include `"pi": {"piContextWindow": 32768, "piCompaction": {"enabled": true,
"reserveTokens": 8192, "keepRecentTokens": 8192}}`. These are SDK token settings,
not the broker's byte ceiling. Omission preserves the pinned catalog and SDK
defaults. The values above illustrate configuration, not a selected schedule or
a guarantee that a request fits: a large recent tool result can still exceed
the byte ceiling. Unknown fields, invalid types, catalog/window bounds and
compaction settings that leave no context room are rejected before model calls.
The exact-image offline Pi preflight also validates configured settings before
broker registration. Plans and results retain requested settings; the wrapper's
terminal event additionally records effective SDK settings.

The explicit local gate is `python3 Tests/pi_context.py`, after
`npm ci --prefix baseline --ignore-scripts` with the pinned Node selected. It uses
the real SDK and a fake local provider, including native compaction and the
unchanged default path; it needs no Docker or Lean build. The regular evaluation
CI does not install those npm dependencies, so this gate is run separately.

## What the measurements mean

| Measure | Interpretation |
| --- | --- |
| Artifact pass | The independent checker accepts the final files. |
| Qualified finish | Artifact pass and normal agent exit, with the declared integrity checks. |
| Cost per qualified finish | Sum of charges for **all** runs in the cohort, including failures, divided by qualified finishes. Undefined if none finish successfully. |
| Time per qualified finish | Total agent elapsed time across the cohort divided by qualified finishes. Also report individual-run times and timeouts. |
| Model attempts and tokens | Count summaries and retries; distinguish ordinary, cache-read and cache-write usage. Missing usage stays unknown. |
| Reliability | Protocol failures, uncertain outcomes, interventions, repeated/lost work and recovery checks. |

Optimize cost and time while holding task success and safety requirements fixed.
Report unknown usage and its reserved allowance separately from known charges;
an accounted reservation is not an invoice. Keep task, model and budget settings
fixed for a controlled comparison, and document differences in the product track.
Repeat selected tasks to expose model variability, without counting repetitions
as new tasks. Preparation, independent grading and documentation-authoring costs
are separate from the agent-run efficiency measure.

## Run and analyze

Use x86_64 Linux with bubblewrap, Python 3, GNU `time`, Node/npm and the pinned
Lean/Rust toolchains. First build the product and proxy using the
[workspace setup](README.md#setup). These commands run from the `eval/`
directory. Initialize [shared accounting](ACCOUNTING.md) before live calls.
Current runs select `--task-context-version 4` explicitly so the frozen plan
matches schema 7's application-neutral operation-time-limit notice and summary/repair text. This applies to `suite.py`,
`public_bench.py run`, and `sustained.py run`; the legacy default remains 1.
The option records the request format for auditing, not a harness behavior change.
Do not change historical plan versions.
This small example uses two development tasks:

```sh
python3 corpus/validate.py --output /tmp/corpus-validation.json
python3 corpus/test_checkers.py

python3 runner/suite.py \
  --task-context-version 4 \
  --key-file /private/anthropic-key --output /private/eval/local \
  --campaign-dir /private/eval/pilot-budget --allocation development \
  --budget 5 --model claude-opus-5-5 --repetitions 1 --tracks product \
  --tasks dev01-inventory-cli dev02-config-overlay
python3 runner/analyze.py /private/eval/local \
  --output /private/eval/local-analysis.json
python3 runner/audit_patches.py /private/eval/local \
  --output /private/eval/patch-audit.json
```

Run output directories must be new. Use `--tasks`, `--engines`, `--tracks` and
`--repetitions` for smaller experiments; keep tuning on development tasks. Plans
record limits, instructions, task selection and binary/source/lock hashes before
execution. Patch-audit flags require manual review and do not change scores.

To use the recorded continuation limits with the current harness and accounting
(a new run, not an exact reproduction of the historical candidate):

```sh
python3 runner/suite.py \
  --task-context-version 4 \
  --key-file /private/anthropic-key --output /private/eval/continuation \
  --campaign-dir /private/eval/pilot-budget --allocation development \
  --budget 5 --tasks dev01-inventory-cli --engines lean --tracks product \
  --repetitions 2 --max-attempts 24 --timeout 600 \
  --yield-after 8 --context-bytes 65536 \
  --compact-at-percent 25 --keep-messages 2 --summary-bytes 6000
python3 runner/audit_continuation.py /private/eval/continuation \
  --output /private/eval/continuation-audit.json
```

The runner resumes exit-75 checkpoints. A sustained-session pass requires task
success, an actual restart and accepted compaction, with replay and counter
checks. Finishing without exercising those events does not pass that gate.

## Public benchmarks

[PUBLIC.md](PUBLIC.md) describes locked images, datasets, preflight, official
verification and recorded setup failures. Docker and the pinned upstream
checkouts/evaluator are required. Supply their locations explicitly:

```sh
python3 runner/public_bench.py preflight \
  --tasks pallets__flask-4045 django__django-11099 \
  --tb-repo /path/to/terminal-bench-2-1 \
  --swe-python /path/to/swe-venv/bin/python --dataset /path/to/swe-dataset.json \
  --output /private/eval/public-preflight
python3 runner/public_bench.py run \
  --task-context-version 4 \
  --tasks pallets__flask-4045 django__django-11099 \
  --campaign-dir /private/eval/pilot-budget --allocation development \
  --tb-repo /path/to/terminal-bench-2-1 \
  --swe-python /path/to/swe-venv/bin/python --dataset /path/to/swe-dataset.json \
  --key-file /private/anthropic-key --output /private/eval/public --budget 12
python3 runner/summarize_public.py /private/eval/public \
  --output /private/eval/public-summary
```

Public defaults use one repetition, both engines and 24 tools. Keep follow-ups
separate; summarize larger-budget diagnostics with `--diagnostic`. Use upstream
verifier results and normal exit as separate measures. The stored stricter
no-test-edit qualifier is not directly comparable: only Lean received that extra
instruction. [Public qualifications and provenance](reports/2026-11-09-public-sample.md).

## Isolation, accounting and interpretation

The host broker keeps the real API key outside candidate environments and counts
every forwarded request, including summaries. Lost usage retains a conservative
reservation. Local agent and checker-worker namespaces separate candidate code
from hidden cases, references and the parent checker. Only allowlisted source
enters grading. This setup does not make the harness itself an OS sandbox.

Keep raw sessions and model content private. Publish reviewed aggregates; retain
failures, timeouts, skipped runs and unknown usage. Each broker has a local ceiling
and all brokers share the durable [campaign ledger](ACCOUNTING.md).
Specify each batch's allocation and budget. The
[campaign ledger](reports/2026-11-09-campaign.json) includes pilots and authoring.

A checker pass describes tested code; a qualified finish also requires normal
agent exit. Four reserved tasks cannot meet the recorded parity gate of at least
30 tasks and a lower 95% bound above −10 percentage points. Bootstrap resampling
clusters by task; repetitions are not independent tasks. The local RSS field
omits the agent and must not be used for a memory comparison.

The earlier [one-task smoke driver](https://github.com/tannerduve/lean-harness/blob/fd7f6cb38cf62ec147186dfec540e32eaeb00c34/eval/runner/live_smoke.py)
is preserved at its historical source revision. Use the current runners for new
work so every live request uses shared accounting.
