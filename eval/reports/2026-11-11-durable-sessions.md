# Durable-session evaluation: 16 runs on four known feature tasks

All 16 planned runs executed. **12 passed the frozen artifact checks, 12 finished
normally, and 5 qualified under the original evaluator.** Separately reviewed
checkpoint-metadata corrections raise qualification to **8/16: Lean 8/12 and Pi
0/4**. Original results and failed audits remain unchanged. All **360 provider
attempts settled for $22.596516**, priced from saved usage at the configured rates,
not an independently verified invoice.

These are four previously observed, self-authored feature tasks on pinned
SWE-bench repository images—not SWE-bench issue scores or held-out tasks. Each
feature ran once in each of four modes; there are no replacements or hidden
retries. This small, uneven product comparison does not establish parity or
native-default performance. The [compact JSON report](2026-11-11-durable-sessions.json)
binds all run metrics, reviews, corrections and source identities to the immutable
private aggregate `660934343258c95d1df1e2d94684a7d59193d99f5492a687bf8e6f4cb71ea570`.

| Repository | Requested feature | Frozen feature checker |
| --- | --- | --- |
| pytest | Atomic JSON collection report, item metadata and full ordered collection errors | 14 cases |
| Pylint | JSON Lines diagnostics, category totals and distinct-file count | 12 cases |
| Sphinx | Atomic link-check report with occurrence locations and incremental freshness | 8 cases |
| SymPy | Coordinate-list matrix import/export, preserving classes and sparse scaling | 28 groups, including 240 generated cases |

Every task also required documentation, regression tests and preserved existing
behavior. Separate pinned upstream commands ran in fresh graders. Sphinx's three
external-Internet tests were excluded before execution. Its empty-input checks
cover a valid project with no links, not an invalid source tree without a master
document.

The model was `claude-opus-5-5`; the Pi baseline was version 1.5.0. Shared ceilings
were 40 provider attempts **including summaries**, 120 tool dispatches, 4,096 output
tokens, 900 seconds and 2 GiB candidate-container memory. Lean used schema 7 and
request-context version 4. Its operation limit was 90 seconds; Pi retained native
or model-supplied tool deadlines. Tool APIs, prompts and isolation differed: Lean
used nested bubblewrap, while Pi used its native tools in ordinary outer Docker.

| Mode | Context and compaction | Planned process restarts |
| --- | --- | --- |
| Lean adequate | 120,000 estimated bytes; 75% trigger; keep 4 messages; summary ≤12,000 bytes | None |
| Lean constrained | 60,000 estimated bytes; 90% trigger; keep 2 messages; summary ≤8,000 bytes | None |
| Lean constrained + restart | Same constrained settings | Yield every 12 durable completions |
| Pi product | Native SDK context management, no virtual-window override; external 144,000-byte request-body cap | None |

The broker body caps were 144,000 bytes for adequate/Pi and 84,000 for constrained
Lean. These external caps differ from Lean's context estimator.

| Mode (4 runs each) | Artifact passes | Normal finishes | Original qualified | Corrected qualified | Total cost | Cost / corrected qualified | Agent seconds / corrected qualified |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Lean adequate | 4 | 4 | 3 | 3 | $5.900560 | $1.966853 | 215.421 |
| Lean constrained | 3 | 4 | 2 | 2 | $5.820008 | $2.910004 | 466.861 |
| Lean constrained + restart | 3 | 4 | 0 | 3 | $6.751948 | $2.250649 | 375.243 |
| Pi product | 2 | 0 | 0 | 0 | $4.124000 | — | — |
| **All 16** | **12** | **12** | **5** | **8** | **$22.596516** | **$2.824565** | **397.800** |

Ratios divide total observed cost or saved agent time across **all outcomes** by
qualified successes; they are not averages restricted to successful runs. Total
agent time was 3,182.400 seconds, and saved preparation-plus-agent run time was
3,287.891 seconds. Neither includes grader/analyst labor or denotes end-to-end
cohort wall time. Exact costs and ratios at their recorded Decimal precision are retained in JSON;
zero-success ratios are undefined.

In the following table, A/C/R/P mean adequate, constrained, constrained + restart,
and Pi product. Calls are provider attempts / tool dispatches. Q is original →
corrected qualification. The JSON includes complete run IDs, timings, usage,
memory and evidence hashes.

| Slot | Task / mode | Artifact / normal | Q | Calls | Summaries / restarts | Cost | Outcome |
| ---: | --- | --- | --- | ---: | ---: | ---: | --- |
| 1 | pytest A | Pass / Yes | Yes → Yes | 19 / 21 | 1 / 0 | $1.384060 | Approved |
| 2 | pytest C | Fail / Yes | No → No | 18 / 22 | 2 / 0 | $0.880224 | Full error-text mismatch |
| 3 | pytest R | Pass / Yes | No → Yes | 32 / 36 | 4 / 13 | $1.508916 | Checkpoint metadata corrected |
| 4 | pytest P | Pass / No | No → No | 18 / 16 | 0 / 0 | $2.062724 | Request-size stop; docs missing |
| 5 | Pylint A | Pass / Yes | No → No | 28 / 28 | 1 / 0 | $1.928972 | Distinct files undercounted |
| 6 | Pylint C | Pass / Yes | No → No | 40 / 48 | 6 / 0 | $2.151292 | Distinct files undercounted |
| 7 | Pylint R | Pass / Yes | No → Yes | 36 / 47 | 6 / 16 | $2.007392 | Checkpoint metadata corrected |
| 8 | Pylint P | Pass / No | No → No | 16 / 17 | 0 / 0 | $1.707872 | Request-size stop; tests/docs incomplete |
| 9 | Sphinx A | Pass / Yes | Yes → Yes | 17 / 15 | 1 / 0 | $1.240612 | Approved |
| 10 | Sphinx C | Pass / Yes | Yes → Yes | 35 / 36 | 5 / 0 | $1.890856 | Approved |
| 11 | Sphinx R | Pass / Yes | No → Yes | 40 / 62 | 7 / 19 | $2.238984 | Checkpoint metadata corrected |
| 12 | Sphinx P | Fail / No | No → No | 2 / 2 | 0 / 0 | $0.141492 | Empty patch; thinking-only length stop |
| 13 | SymPy A | Pass / Yes | Yes → Yes | 19 / 22 | 1 / 0 | $1.346916 | Approved |
| 14 | SymPy C | Pass / Yes | Yes → Yes | 17 / 21 | 2 / 0 | $0.897636 | Approved |
| 15 | SymPy R | Fail / Yes | No → No | 19 / 22 | 2 / 8 | $0.996656 | Scalar strings incorrectly rejected |
| 16 | SymPy P | Fail / No | No → No | 4 / 4 | 0 / 0 | $0.211912 | Empty patch; thinking-only length stop |

The evaluator's compact checkpoint collector omitted the schema-7 `turn` field.
For slots 3, 7 and 11, independent reconstruction inspected and replayed each
exact retained journal prefix, supplied only the missing metadata, and reran the
unchanged qualification logic in separate derived records. Their artifacts and
manual approvals did not change. SymPy restart's eight exact prefix states also
matched, but strict scalar sympification rejected string values such as `"2/3"`;
its failed feature checks and qualification remain false.

The Pylint checker had a real coverage gap. Five supplemental fresh-grader
executions tested the four unchanged candidates and the frozen reference on two
standalone files sharing a basename. The adequate and constrained Lean candidates
**and the reference** reported one file despite diagnostics from both; the restart
and Pi candidates reported two. The retained supplement is bound by
`6a84957d7577b0df59cca87f2aed19b640e0bd5ea266a06bd5ade63626315bc6`.
Original checker passes are preserved; this is additional evidence supporting the
independent rejections, not a repaired oracle silently substituted into scores.

Pi's four abnormal finishes have two different causes. pytest and Pylint hit the
external request-size limit; Sphinx and SymPy ended with `max_tokens`/`length`
responses whose 4,096 output tokens were all reported as thinking, with no patch.
The frozen shorthand that Pi's off setting mapped to low effort was incomplete:
an unpaid, pinned-SDK construction probe produced adaptive thinking with
**top-level effort low and system-message effort high**. Historical request-setting
fields were not retained, so this proves neither their exact bytes nor effective
provider interpretation. No matched-effort claim is made. Outbound body hashes
and matched Lean context digests support their narrower recorded-context audit;
they do not expose missing effort fields.

All **38 accepted summaries** were reviewed against their actual source ranges and
next complete contexts; Pi produced none. Requirements and useful continuation
were often retained, but reviews also found factual inaccuracies, omitted detail
and partly retained constraints. For example, pytest restart misattributed earlier
successful edits to a rejected batch; Sphinx constrained abbreviated an ordering
rule. Qualification combines task artifacts, normal completion, settled execution
and applicable audit/review criteria. It does **not** certify every instruction was
followed or every summary was accurate. No task failure is attributed to compaction
without evidence. The 56 observed restarts were scheduled durable suspend/resume
operations, not random crashes or physical power-loss tests.

Provider unknown usage, Lean core unknown usage, active requests and unsettled
requests were all zero at closure. Operator and review declarations report zero
task interventions; these are explicit declarations, not proof against all outside
interference. The twelve Lean journals independently contain zero additional
`user_turn`, `recovery` or `resolution` records; those counts are separate from
planned restarts and from Pi's native session format. Memory was sampled whole-
container `memory.current`, including page cache: the largest observation was
746,749,952 bytes (about 712.2 MiB), not process RSS or a guaranteed peak.

The frozen local candidate was based on `cb460b7` plus the recorded source changes,
with executable SHA `25a816665c95f9011183091723fd6bc3f62db15f954fb5c199109d784aa025e4`.
The source inventory/archive identifies the actual tested tree; the base commit
alone does not. Separate [local proof, persistence and runtime validation](../../docs/reports/2026-11-11-durable-sessions.md)
covers mechanisms beyond these coding tasks. Subsequent
[evaluator fixes and focused tests](2026-11-11-evaluator-fixes.json) address the
checkpoint collector and bounded request-settings evidence; they neither rewrite
these runs nor retroactively reveal historical settings. Earlier November 9
reports remain historical, and this cohort makes no claim about the unopened
held-out comparison.
