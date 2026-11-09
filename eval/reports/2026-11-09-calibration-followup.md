# Two-run follow-up: both development tasks qualified

The Lean harness finished both runs normally, passed their artifact checks, and
received independent qualification for both. These were previously observed,
self-authored pytest and Sphinx feature tasks on pinned SWE-bench repository
images. They are development evidence, not held-out issue scores, a Pi comparison,
or completion of the full 16-run sustained-use gate.

| Task and mode | Feature checks | Selected upstream tests | Model / tool calls | Summaries / restarts | Normal / qualified | Cost |
| --- | --- | --- | ---: | ---: | --- | ---: |
| pytest collection report · adequate context | 14/14 | 70 passed, 1 xfailed | 20 / 25 | 1 / 0 | Yes / Yes | $1.644740 |
| Sphinx link-check report · constrained context + restarts | 8/8 | 24 passed, 3 deselected | 40 / 48 | 5 / 17 | Yes / Yes | $2.321308 |

Qualification combines normal completion, automated checks, applicable session
checks, and independent patch review. Codex agents reviewed the saved patches,
tests and documentation; no human review is asserted. The Sphinx exclusions were
fixed before execution because those tests require external Internet access.
Its empty-input checks cover a valid project with no links, not a source directory
without a master document. The [JSON report](2026-11-09-calibration-followup.json)
binds the original results, reviews, audits and retained evidence by hash.

Sphinx passed its applicable continuation gate: five accepted summaries and 17
durable restarts, with useful implementation and focused testing afterward.
Independent reconstruction verified summary source ranges, subsequent contexts,
checkpoint replay and budget notices. Qualitative review retained the empty-input
interpretation as a limitation. The restart gate was **inapplicable** to pytest's
adequate-context mode; its one summary is not a restart-gate pass.

Neither run produced a typed timeout or skipped tool suffix. These successes do
not demonstrate live coverage of the corrected timeout path or establish why the
earlier runs failed. The [four-run calibration](2026-11-09-calibration.md), its
failures and all original result rows remain unchanged; qualification is recorded
separately.

Candidate `587dcff` used schema 5, task-context version 3 and `claude-opus-5-5`.
Each run allowed 40 provider attempts including summaries, 120 tools, 4,096 output
tokens and 900 seconds, with zero retries. Bubblewrap commands had a 90-second
limit. Context allowances were 120,000/60,000 estimated bytes, with compaction at
75%/90%; Sphinx yielded every 12 durable completions.

All **60 provider requests settled for $3.966048**, a frozen-rate estimate rather
than an invoice. Both planned slots ran; costs were known and cleanup settled.
Campaign spending reached **$65.072492 of $150**, within this cohort's $4.75 cap.

The audits establish exact correspondence with locally recorded requests, not
independent wire equality: outbound bodies and context digests were not retained.
A future transport-digest fix cannot upgrade these rows retroactively. The full
16-run sustained gate, original 72-run held-out comparison and this transport
evidence requirement remain outstanding.
