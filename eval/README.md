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
| Product | Pi's coding-agent SDK and Lean use their respective tools, prompts and context policies under shared limits and zero retries. Pi extensions, skills and ambient context files are disabled. Pi requests adaptive reasoning at low effort for this model; Lean does not request that mode. |

Defaults: `claude-opus-5-5`, 12 provider attempts, 40 tools, 4,096 output tokens,
120,000 estimated context bytes, 90 seconds per operation and 300 seconds per run.
Product context policies differ; both also face a broker request-byte ceiling.
The full schedule is **16 tasks × 2 engines × 2 tracks × 2 repetitions = 128 runs**.

Pi **1.5.0** and its dependencies are [locked](baseline/package-lock.json).
Node/Pi are evaluation dependencies, not production harness dependencies.

## Run and analyze

Use x86_64 Linux with bubblewrap, Python 3, GNU `time`, Node/npm and the pinned
Lean/Rust toolchains. These commands make real model calls only at `suite.py`:

```sh
lake build harness eval_tools
npm ci --prefix eval/baseline --ignore-scripts
python3 eval/corpus/validate.py --output /tmp/corpus-validation.json
python3 eval/corpus/test_checkers.py

python3 eval/runner/suite.py \
  --key-file /private/anthropic-key --output /private/eval/local \
  --budget 100 --model claude-opus-5-5 --repetitions 2
python3 eval/runner/analyze.py /private/eval/local \
  --output /private/eval/local-analysis.json
python3 eval/runner/audit_patches.py /private/eval/local \
  --output /private/eval/patch-audit.json
```

Run output directories must be new. Use `--tasks`, `--engines`, `--tracks` and
`--repetitions` for smaller experiments; keep tuning on development tasks. Plans
record limits, instructions, task selection and binary/source/lock hashes before
execution. Patch-audit flags require manual review and do not change scores.

The recorded continuation trials used these settings:

```sh
python3 eval/runner/suite.py \
  --key-file /private/anthropic-key --output /private/eval/continuation \
  --budget 5 --tasks dev01-inventory-cli --engines lean --tracks product \
  --repetitions 2 --max-attempts 24 --timeout 600 \
  --yield-after 8 --context-bytes 65536 \
  --compact-at-percent 25 --keep-messages 2 --summary-bytes 6000
python3 eval/runner/audit_continuation.py /private/eval/continuation \
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
python3 eval/runner/public_bench.py preflight \
  --tb-repo /path/to/terminal-bench-2-1 \
  --swe-python /path/to/swe-venv/bin/python --dataset /path/to/swe-dataset.json \
  --output /private/eval/public-preflight
python3 eval/runner/public_bench.py run \
  --tb-repo /path/to/terminal-bench-2-1 \
  --swe-python /path/to/swe-venv/bin/python --dataset /path/to/swe-dataset.json \
  --key-file /private/anthropic-key --output /private/eval/public --budget 35
python3 eval/runner/summarize_public.py /private/eval/public \
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
failures, timeouts, skipped runs and unknown usage. Broker budgets are separate,
not a global billing cap: reconcile existing ledgers before another batch.
`suite.py` defaults to $150, so specify each batch's allocation. The
[campaign ledger](reports/2026-11-09-campaign.json) includes pilots and authoring.

A checker pass describes tested code; a qualified finish also requires normal
agent exit. Four reserved tasks cannot meet the recorded parity gate of at least
30 tasks and a lower 95% bound above −10 percentage points. Bootstrap resampling
clusters by task; repetitions are not independent tasks. The local RSS field
omits the agent and must not be used for a memory comparison.

The earlier [one-task smoke test](runner/live_smoke.py) uses an older isolation
arrangement and is separate from these experiments.
