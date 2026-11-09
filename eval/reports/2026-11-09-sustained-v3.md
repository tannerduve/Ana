# Sustained-session trial: stopped, not qualified

This trial stopped after the Pi launcher failed to start Node inside its task
container. Five of 16 planned runs started; 11 remain unrun. The three completed
Lean runs also failed to finish their tasks. **This candidate did not meet the
sustained-use gate.** Original results are preserved in the
[run report](2026-11-09-sustained-v3.json).

The workload was four self-authored features in pytest, Pylint, Sphinx and
SymPy. Each had three Lean modes—adequate context, constrained context, and
constrained context with scheduled restarts—and one ordinary Pi run. These are
separate from the unopened held-out SWE-bench comparison.

| Task / mode | Model calls | Summaries / verified restarts | Cost | Observed outcome |
| --- | ---: | ---: | ---: | --- |
| pytest / Lean adequate | 8 | 0 / 0 | $0.456460 | Rejected an edit batch containing a shortened preimage hash; incomplete patch |
| pytest / Lean constrained | 19 | 2 / 0 | $1.072580 | Rejected a malformed stream; patch also had conflicting plugin registration |
| pytest / Lean constrained + restart | 15 | 2 / 5 | $0.903112 | Rejected a malformed stream; patch failed collection-error formatting and omitted required docs/tests |
| pytest / Pi | 0 | — | $0 | Launcher failed: Node could not load `libnode.so.109` |
| Pylint / Lean adequate | 11 | Not audited | $0.765756 | Interrupted after the launcher problem was identified; patch/session capture was lost |
| Remaining Pylint, Sphinx and SymPy slots | 0 | — | $0 | 11 unrun |

All **53 provider requests** have settled usage, totaling **$3.197908**. Calls
include summaries. The two stream failures each leave one usage entry unknown
to the Lean core; the external evaluation broker received their usage and
accounted for their cost. These are distinct ledgers.

## What worked, and what failed

All three completed Lean sessions passed replay and independent session-integrity
checks. The restart run crossed two accepted summaries and five verified
checkpoints. That exercises continuation, but does not establish successful
long-task performance. Independent model reviewers rejected all three saved
patches. The Pylint patch was unavailable for review.

The stream error was `message delta before content block stop`. Both affected
responses reached the configured output ceiling, but the raw stream was not
retained, so truncation as the cause remains unconfirmed. No partial tool batch
was admitted. Review of both constrained-run summaries found the five critical
requirements still present; it did not establish that compaction caused the
later mistakes.

The Pi failure occurred before any model call. The coordinator's restricted
environment selected the system Node executable instead of the installed Node
distribution. It is an evaluation infrastructure failure, not a Pi task result.
Stopping the next run exposed another evaluator defect: interruption bypassed
patch/session capture before container cleanup. Cleanup observations and that
missing evidence remain visible in the report.

## Scope

The frozen candidate was `eed86661`, from source `afa9028`, with Pi 1.5.0 and
`claude-opus-5-5`. Each run allowed 40 model attempts, 120 tools, 4,096 output
tokens and 900 seconds. Lean context allowances were 120,000 or 60,000 bytes;
the restart mode yielded after every 12 durable completions. Pi used its normal
context behavior. Prompts, tools, effort and isolation differed, as recorded in
the frozen protocol.

Fixes and any later runs belong to a new candidate and cohort. This incomplete
trial supports neither a success-rate comparison with Pi nor a release claim.
