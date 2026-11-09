# Sustained-session v4: useful patches, gate not met

The Lean harness and Pi started **12 of 16 planned runs** on self-authored
features in pytest, Pylint, Sphinx and SymPy. The shared long-task allocation
stopped the cohort before any SymPy run. **The sustained-use gate failed; the
held-out agent comparison remains unopened.** This is a diagnostic cohort,
not a Pi parity result. See the [machine-readable report](2026-11-09-sustained-v4.json)
for hashes, per-run evidence and separate qualification outcomes.

Each task had three Lean modes—adequate context, constrained context, and
constrained context with scheduled restarts—and one Pi product run.

| Task | Planned | Started | Unrun | Checker passes | Normal finishes | Qualified: original → corrected |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| pytest: JSON collection report | 4 | 4 | 0 | 3 | 2 | 1 → 2 |
| Pylint: JSONL diagnostic reporter | 4 | 4 | 0 | 4 | 0 | 0 → 0 |
| Sphinx: JSON link-check report | 4 | 4 | 0 | 4 | 0 | 0 → 0 |
| SymPy: coordinate-list matrix import/export | 4 | 0 | 4 | — | — | — |
| **Total** | **16** | **12** | **4** | **11** | **2** | **1 → 2** |

A checker pass means the saved patch passed the independent automated checks.
Qualification additionally requires normal completion, session checks where
applicable, and independent review of the complete requested deliverable.
Missing documentation or regression tests therefore matters even when the
feature checker passes. The reviewers were Codex agents; these are model
judgments, not human reviews or proofs.

The frozen evaluator had a circular dependency: continuation auditing required
qualified success before qualification could accept that audit. Original
qualification remains **1/12 started, or 1/16 planned**. A separate, hash-bound
correction adds the pytest restart run: **2/12 started, or 2/16 planned**.
It used saved evidence, made no new model calls, and changed no original result.

All three started restart trials crossed seven accepted summaries and performed
useful work after restarting, with 15, 16 and 16 checkpoints. Only pytest passed
the corrected strict audit and complete artifact review; three approved restart
artifacts and all four trials were required. Review covered all 44 accepted
summaries. Critical requirement groups remained in the next contexts, although
some prior facts were omitted; the review does not establish that omissions
caused later failures.

All **333 provider calls** settled for **$23.878448**. The final request needed
a **$1.169232** reservation when **$0.923644** remained in the $28 cumulative
long-task allocation. It was refused, preserving four explicit unrun slots.
This was a spending limit, not an accounting failure. Six rejected responses
left usage unknown to the Lean core; their provider costs were known to the
broker. All nine Lean sessions passed replay/integrity checks, and recorded
owned-container cleanup and image removal settled.

The frozen candidate was `77f76024`, source `d00501e`, with `claude-opus-5-5`
and Pi 1.5.0. Limits were 40 model attempts, 120 tools, 4,096 output tokens and
900 seconds. Lean used 120,000/60,000-byte context estimates. Pi retained native
context management, but its pytest and Pylint runs hit the external
**144,000-byte request-body ceiling**; Sphinx hit spending admission. None of
those Pi runs finished normally. These caps, differing effort/tools/isolation,
and the unfinished schedule limit comparisons. Later candidate or setting
changes require a separately versioned cohort.
