# Four-run calibration: no qualified finishes

Four development runs tested the revised Lean harness and an explicit Pi context
configuration on three previously observed repository features. **None qualified.**
Two patches passed the automated artifact checks; independent review found one
complete requested change. The held-out comparison remains unopened.

| Run | Feature checks | Selected tests | Normal finish | Patch review | Cost |
| --- | --- | --- | --- | --- | ---: |
| pytest · Lean, adequate context | Failed: option missing | Not run | No: interrupted command | Reject | $1.08 |
| Pylint · Lean, constrained context | 12/12 | 53 passed, including 7 new | No: exit 137 | Approve | $1.47 |
| Sphinx · Lean, constrained context + restarts | 8/8 | Timed out | No: interrupted command | Reject | $1.35 |
| Pylint · Pi | 12/12 | 46 existing tests passed | No: output-length limit | Reject | $3.23 |

Automated artifact acceptance requires both feature checks and the selected test
suite. Qualification also requires a normal finish, applicable session checks,
and independent review of the requested implementation, tests and documentation.
The reviewers were Codex agents; their judgments are recorded separately from
automated results in the [machine-readable report](2026-11-09-calibration.json).

## What failed

- **pytest:** one command chained two broad test runs around `git stash` and
  `git stash pop`. It exceeded the 90-second command limit. Registration and
  documentation edits present earlier were absent from the final patch, consistent
  with an interrupted stash/restore sequence. Git metadata was not captured, so
  the exact stash state is unproven.
- **Lean Pylint:** the complete patch passed review, but a later `pytest -n auto`
  command coincided with abrupt termination. Sampled container memory reached its
  2 GiB cap. OOM counters were not retained, so the cause of exit 137 is unproven.
  The journal replays exactly and retains an unresolved tool intent.
- **Sphinx:** the feature passed its checks, but review found two authored-test
  defects: reusing a builder after its workers shut down, and conflating `/ok`
  with `/ok#frag` when counting requests. Both the agent's test command and the
  selected verification suite timed out. The blocked stack was not retained.
- **Pi Pylint:** the patch omitted required documentation and focused tests.
  Five later summary calls hit our 4,096-token ceiling, leaving the previous
  context in place. As that context grew, the SDK reduced the final task replies
  to 201 and then 1 output token. Offline reconstruction with the pinned SDK
  reproduced those limits exactly.

## Context and recovery evidence

The Lean Pylint run crossed four compactions; Sphinx crossed three and ten durable
restarts. Their source/context mappings were checked, and all ten Sphinx checkpoint
and replay pairs matched. Critical task requirements survived the reviewed
summaries, but some implementation facts were misstated or omitted. In particular,
one Sphinx summary omitted previously observed worker-shutdown behavior. These
observations do not establish that compaction caused the later test failures.

Pi performed three native compactions. Its summaries retained the documentation
and test requirements, alongside some inaccurate repository facts. This review
does not supply Lean-style replay guarantees for Pi.

The Lean response-repair mechanism was not exercised in these runs. Its existing
deterministic tests remain separate evidence. The sustained-use gate was not met.

## Configuration and accounting

The candidate was `d8ba725`, schema 4, with task-context version 2, model
`claude-opus-5-5` and Pi 1.5.0. Each run allowed 40 provider attempts, including
summaries, 120 tools, 4,096 output tokens and 900 seconds. Lean commands had a
90-second limit. Lean context allowances were 120,000 or 60,000 estimated bytes;
Pi used a 32,768-token window with 8,192-token reserve and retained suffix settings.

These were targeted development trials with different context units, effort,
per-tool timeout behavior and isolation: Lean used nested bubblewrap, while Pi
used its native tools in the outer container. They do not establish comparative
task success or parity.

All **101 provider attempts settled for $7.133056 at the frozen prices**. All four planned runs were
recorded, with no unknown provider costs or unresolved container cleanup. Campaign
spending at closure was **$61.106444 of the authorized $150**. Original outcomes
and the independent reviews are retained with hashes; later changes receive
separate evidence.
