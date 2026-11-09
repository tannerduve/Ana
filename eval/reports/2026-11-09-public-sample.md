# Public benchmark sample

We compared the Lean harness with Pi on Flask blueprints, Django username validation, a self-signed certificate, and a Coq addition proof. These are **selected SWE-bench Lite tasks** graded by the official SWE-bench evaluator, plus two Terminal-Bench 2.1 tasks using upstream verifiers. Neither full suite was run; this small sample does not establish general parity.

Original results below show **official passes / planned attempts**, including setup failures. “Finished normally” means exit code 0; it does not mean the patch passed its tests.

| Task | Benchmark | Lean: original attempts | Pi: original attempts |
| --- | --- | --- | --- |
| Flask blueprints | SWE-bench Lite | 0/2 | 0/2 |
| Django validators (additional) | SWE-bench Lite | 2/2 | 2/2 |
| Self-signed certificate | Terminal-Bench 2.1 | 2/2 | 2/2 |
| Coq addition proof | Terminal-Bench 2.1 | 1/2; 1 setup failure | 1/2; 1 setup failure |
| Requests redirects | SWE-bench Lite | Not run: preflight failed | Not run: preflight failed |

Django was an additional selection made before its model runs after Requests failed preflight. Requests' HTTPBIN dependency now rejects a required redirect; both planned runs remain recorded. Coq's two setup failures occurred before model calls. After a successful baseline/reference gate with HTTPS and main-only Ubuntu package indexes, one separate rerun per engine passed. Original failures were retained.

| Stage | Agent executions | Official passes | Finished normally | Cost |
| --- | --- | --- | --- | --- |
| Initial attempts | 14 | 10 | 12 | $2.797756 |
| Coq reruns | 2 | 2 | 2 | $0.132176 |
| Total | 16 | 12 | 14 | $2.929932 |

There were 18 planned slots: 14 initial executions, 2 setup failures, and 2 Requests exclusions. The 2 reruns add attempts, not replacements. Cost uses configured prices and provider usage; unknown-usage requests: 0. The separate [Flask budget diagnostic](2026-11-09-flask-budget-diagnostic.md) is excluded here.

All four runnable tasks failed unchanged baselines and passed upstream reference solutions. Official checks ran in fresh images with unchanged verifiers. The [supplemental Coq audit](2026-11-09-public-coq-audit.json) checked the required theorem type and closed assumptions for all four saved proofs; early artifacts were audited afterwards.

Both engines used Claude Opus 5.5 in product mode: 12 provider attempts, 24 tools, and 300 agent seconds, with 4096 output tokens. Summaries and SDK retries count as attempts. Engine order reversed on the second repetition. Product prompts, tools, and thinking defaults can differ.

- Lean estimates context against 120,000 bytes; Pi keeps its native context policy. Both face a separate 144,000-byte broker request ceiling.
- Only Lean received the extra instruction forbidding test edits. The stricter stored `success` flag is therefore not comparable; the tables use official verifier outcomes.
- Elapsed time includes setup and excludes grading. Peak memory was not measured.
- The first six-run plan omitted the runner-source hash. It recorded binary, tool, Pi-lock, and benchmark-lock identities; later plans also hash the runner.

[Run JSON](2026-11-09-public-sample.json) retains individual results and hashes; [preflight history](2026-11-09-public-preflight.json) preserves setup attempts and interruptions. [Pinned assets and instructions](../PUBLIC.md) explain reproduction. Raw transcripts and private keys are omitted.
