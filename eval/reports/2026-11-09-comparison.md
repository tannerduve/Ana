# Evaluation — November 9, 2026

On the local corpus, the Lean harness finished normally with passing code in
**61/64 runs**, versus **63/64 for Pi**. The final code passed the checker in
**63/64 runs for each engine**. These results establish neither production
readiness nor parity.

“Lean” means this harness running **Claude Opus 5.5**. Task
languages include Python, JavaScript, Rust and Lean. Pi also used Opus 5.5;
its version was pinned to **1.5.0**.

## What ran

| Suite | Runs | Purpose |
| --- | --- | --- |
| Local comparison | **128** = 16 tasks × 2 engines × 2 tracks × 2 repetitions | Compare coding results and execution behavior. |
| Continuation | **2** Lean runs | Force compaction and durable restarts on the inventory CLI task. |
| Selected public tasks | **16** agent executions, including 2 retries | Run official Terminal-Bench 2.1 and SWE-bench Lite verifiers. Setup failures remain recorded separately. |
| Flask follow-up | **4** runs: 2 per engine | Test larger budgets after the original failures; excluded from original scores. |

Four pilot runs and two documentation-authoring requests are excluded from task
scores but included in campaign spending.

## Local results

A **checker pass** means the final files passed independent tests and protected-file
checks. A **qualified finish** additionally requires normal agent exit. Neither
establishes correctness beyond the checks performed.

| Track | Engine | Checker passes | Qualified finishes |
| --- | --- | --- | --- |
| Controlled | Lean | 32/32 | 31/32 |
| Controlled | Pi | 32/32 | 32/32 |
| Product | Lean | 31/32 | 30/32 |
| Product | Pi | 31/32 | 31/32 |

Controlled runs aligned tools, instructions, context estimation and provider
settings. Product runs used each engine's own tools, prompts and context behavior
under shared ceilings: 12 provider attempts, 40 tools, 4,096 output tokens and
300 seconds. Product reasoning settings differ. [Protocol and commands](../README.md).

All 128 runs completed without timeouts, infrastructure failures,
unknown usage or human intervention. Replay matched all 64 Lean sessions.
The four unqualified finishes were:

- Two Lean runs produced passing Rust patches, then stopped when validation
  rejected scratch-file requests outside the workspace.
- One Lean settings patch failed cases that conflict with a plausible reading of
  “dictionary of dictionaries.” The frozen failure remains a specification/checker ambiguity.
- One Pi query-parser patch returned strings for singleton keys where the starter
  API and checker expected arrays; the task prose left that detail implicit.

[Manual review](2026-11-09-patch-audit.json) found no protected-file changes or
checker bypasses. A separate [post-hoc numerical probe](2026-11-09-window-posthoc.json)
failed **4/8** moving-window solutions that passed their original checks. Frozen
scores are unchanged; checker-passing code is not necessarily correct.

Four tasks were reserved. The parity gate required at least
30 and a 10-percentage-point regression margin. This corpus cannot meet it.
[Counts, timings, costs and descriptive uncertainty](2026-11-09-comparison.json).

## Continuation and public tasks

**2/2 continuation runs passed**, including independent journal audits. Each
installed four summaries and crossed four durable restart checkpoints. These
forced trials exercise the mechanism, not general summary fidelity.
[Continuation evidence](2026-11-09-continuation-audit.json).

The [public sample](2026-11-09-public-sample.md) produced 12 upstream passes across
16 executions. Two Coq setup failures and their retries remain separate; two
Requests slots never ran because preflight failed. Django was an
additional task. Both engines failed both original Flask repetitions.

With unchanged binaries and prompts, the [Flask follow-up](2026-11-09-flask-budget-diagnostic.md)
doubled public limits to 24 attempts and 48 tools. All four runs finished normally;
Lean passed **0/2**, Pi **1/2**. More budget alone did not resolve Lean's failure.

## Limits and cost

**Agent peak memory is unmeasured**: the local RSS field captured the supervisor,
not the agent. [Probe](2026-11-09-memory-probe.json). Deterministic tests and selected
Lean proofs provide separate evidence; their scope is documented in the
[gate report](2026-11-09-sustained-gates.md) and [Safety.md](../../docs/Safety.md).

Total API accounting was **$19.211732**, including pilots and authoring. All
737 requests reported usage. This uses configured token prices, not a provider
invoice. [Campaign ledger](2026-11-09-campaign.json).
