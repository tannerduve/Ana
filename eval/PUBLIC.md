# Public benchmark sample

This runner compares Lean Harness and Pi on a few public coding tasks. Selected
SWE-bench Lite tasks use the [official SWE-bench evaluator](https://www.swebench.com/SWE-bench/guides/evaluation/);
Terminal-Bench 2.1 tasks use their [upstream verifiers](https://github.com/harbor-framework/terminal-bench-2-1).
It does **not** run either complete suite or establish general parity.

| Task | What the agent does | Selection |
| --- | --- | --- |
| `pallets__flask-4045` | Fix Flask blueprint validation | Original sample |
| `django__django-11099` | Fix Django username validation | Additional task, selected before model runs |
| `openssl-selfsigned-cert` | Create a self-signed certificate | Original sample |
| `prove-plus-comm` | Complete a Coq addition proof | Original sample; two setup failures and separate reruns |
| `psf__requests-2317` | Fix Requests redirect behavior | Blocked at preflight; no model runs |

Read the [public results](reports/2026-11-09-public-sample.md) and the separate
[Flask budget diagnostic](reports/2026-11-09-flask-budget-diagnostic.md).

[public-lock.json](public-lock.json) pins dataset and repository revisions, base
commits, image digests, evaluator versions, verifier hashes, and time allowances.
Reproduction requires those images, a checkout of the pinned Terminal-Bench repo,
a Python environment containing the pinned SWE-bench evaluator, and a JSON export
of the selected dataset rows. Set paths with `--tb-repo`, `--swe-python`, and
`--dataset`. Example for the single Flask task:

```sh
python3 eval/runner/public_bench.py preflight \
  --tasks pallets__flask-4045 --output /tmp/flask-preflight
python3 eval/runner/public_bench.py run \
  --tasks pallets__flask-4045 --output /tmp/flask-runs \
  --key-file /private/path/to/key --budget 5 --repetitions 1
```

Preflight checks that the unchanged baseline fails and the upstream reference
solution passes. References never enter agent containers. Requests remained
blocked because its external HTTPBIN service rejected a required redirect.
Django was an additional selection; it did not erase Requests from the plan.
Coq reruns used explicit `--apt-https --apt-main-only` setup after baseline/reference
checks passed: curl's dependencies are in Ubuntu's main component, and Coq is
already installed. Official task files and verifier scripts stayed unchanged.
[Setup history](reports/2026-11-09-public-preflight.json) retains failures and
interrupted diagnostics.

| Profile | Provider attempts | Tool calls | Output tokens | Agent seconds |
| --- | --- | --- | --- | --- |
| Public comparison | 12 | 24 | 4096 | 300 |
| Separate Flask diagnostic | 24 | 48 | 4096 | 300 |

Both use Claude Opus 5.5 in product mode; prompts, tools, and thinking defaults can
differ. Lean estimates context against 120,000 bytes; Pi retains its native
policy. Both face a separate 144,000-byte broker request ceiling. Summaries and
SDK retries count as provider attempts.

The host broker holds the API credential. Containers receive a scoped endpoint,
not a credential mount, but use host networking. Remote repository history is
removed before SWE runs. After agents stop, artifacts are graded in fresh official
images. Coq also receives a separate [theorem-type and assumptions audit](reports/2026-11-09-public-coq-audit.json).

Use official passes and process exits separately: finishing normally does not
mean a correct patch. The stricter stored `success` flag rejects test edits, but
only Lean received that extra instruction, so this flag is not directly comparable.
Elapsed time includes setup and excludes grading; memory was not measured.
The first six-run plan lacks a runner-source hash; later plans include it.

Run JSON preserves results, costs, and recorded hashes. Raw transcripts and private
keys remain outside committed reports. The runner requires 4 GiB free disk and
removes only containers and images it creates.
