# Public benchmark sample

The recorded sample compares Lean Harness and Pi on a few public coding tasks.
SWE-bench Lite tasks used the [official SWE-bench evaluator](https://www.swebench.com/SWE-bench/guides/evaluation/);
Terminal-Bench 2.1 tasks used their [upstream verifiers](https://github.com/harbor-framework/terminal-bench-2-1).
Neither complete suite was run, and the sample does not establish general parity.

Current paid execution supports repository tasks. It captures bounded workspace
snapshots, stops the candidate, and constructs its patch using trusted host Git.
Candidate Git configuration, hooks and filters cannot participate in extraction.
Terminal-Bench execution is disabled pending an equivalent artifact-export path;
its historical results and offline verifiers remain available.

| Task | What the agent does | Selection |
| --- | --- | --- |
| `pallets__flask-4045` | Fix Flask blueprint validation | Original sample |
| `django__django-11099` | Fix Django username validation | Additional task, selected before model runs |
| `openssl-selfsigned-cert` | Create a self-signed certificate | Original sample |
| `prove-plus-comm` | Complete a Coq addition proof | Original sample; two setup failures and separate reruns |
| `psf__requests-2317` | Fix Requests redirect behavior | Blocked at preflight; no model runs |

Read the [public results](reports/2026-11-09-public-sample.md) and the separate
[Flask budget diagnostic](reports/2026-11-09-flask-budget-diagnostic.md).
The later [four-repository development calibration](reports/2026-11-09-development-v2.md)
retains its own frozen settings and original test-file qualification.

[public-lock.json](public-lock.json) pins dataset and repository revisions, base
commits, image digests, evaluator versions, verifier hashes, and time allowances.
Reproduction requires those images, a checkout of the pinned Terminal-Bench repo,
a Python environment containing the pinned SWE-bench evaluator, and a JSON export
of the selected dataset rows. Complete the [workspace setup](README.md#setup)
and use the enclosing built product checkout. Set benchmark paths
with `--tb-repo`, `--swe-python`, and `--dataset`. Example for the single Flask task:

```sh
python3 runner/public_bench.py preflight \
  --tasks pallets__flask-4045 --output /tmp/flask-preflight
python3 runner/public_bench.py run \
  --task-context-version 4 \
  --campaign-dir /private/eval/pilot-budget --allocation development \
  --tasks pallets__flask-4045 --output /tmp/flask-runs \
  --key-file /private/path/to/key --budget 5 --repetitions 1
```

Initialize the [shared spending ledger](ACCOUNTING.md) before `run`.
Version 3 records the current harness's request format for auditing. The legacy
CLI default remains 1; retain original versions when inspecting historical plans.
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

Both recorded profiles used Claude Opus 5.5 in product mode; prompts, tools, and thinking defaults can
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
In that sample, elapsed time includes setup and excludes grading; memory was not measured.
The first six-run plan lacks a runner-source hash; later plans include it.

Run JSON preserves results, costs, and recorded hashes. Raw transcripts and private
keys remain outside committed reports. The runner requires 4 GiB free disk and
removes only containers and images it creates.

## Interrupted evaluation runs

Each invocation writes `owned-containers.jsonl` before creating candidate or
profile containers. Cleanup checks their exact ownership labels; it never infers
ownership from a global list of newly created containers. An unacknowledged create
remains uncertain when no matching container is observed. Discovery, journal or
cleanup failures stop further paid work.

Missing or unpriceable provider usage also stops further calls and runs. The
relay retains the request's full cost reservation and records unsettled
accounting. It still preserves the stopped candidate's session and patch for
inspection; an artifact pass cannot qualify a run with unsettled accounting.

This covers containers created by this runner. The official SWE-bench evaluator
also creates grader containers through its own SDK; those require separate
inspection after a forced stop. A cleaned-up candidate does not establish that
every grader process has stopped.

The [local interruption gate](reports/2026-11-09-evaluation-interruption.json)
uses real containers and a fake provider. With Ubuntu 24.04 already cached, run:

```sh
HARNESS_INTERRUPT_IMAGE="$(docker image inspect --format '{{.Id}}' ubuntu:24.04)" \
  python3 Tests/evaluation_interrupt.py
```

The test makes no paid calls and never pulls an image. It is separate from the
Docker-free evaluation unit suite in CI.

## Prospective v3 patch review

New repository runs permit regression additions in existing files and justified
expected-output changes for the requested behavior. They prohibit unrelated test
weakening, deletion, checker bypass and changes to protected grading infrastructure.
The same task requirements go to both engines; Lean's extra system prompt no
longer contradicts them. This policy does not reinterpret any recorded v2 result.

Raw `result.json` preserves official checks, process exit, accounting and session
audit separately. Its `success: false` means qualification is pending, not that
the artifact necessarily failed. Every patch needs an independent evaluator review,
including patches with no detected test changes. Review the complete patch against
the task, examine changes to existing assertions and checker execution, and record
specific reasons. A file-name heuristic never approves a patch.

```sh
python3 runner/patch_review.py template /private/run --output /private/review.json
# An independent evaluator completes the review outside the candidate workspace.
python3 runner/patch_review.py qualify /private/run \
  --review /private/review.json --output /private/qualified-result.json
```

The review binds the exact result and candidate-patch hashes. Qualification also
requires passing artifact checks, a normal finish, settled execution and known
usage, plus Lean's session audit and the continuation audit where required.
Approval cannot override those checks. The command writes a new file and refuses
to overwrite existing evidence. Report `qualified_success` separately from the
original raw fields. The evaluator and its review storage are trusted; hashes
establish which artifact was reviewed, not the review's correctness.

## Runtime and response diagnostics

New campaigns pin a dedicated Node distribution and run the installed Pi SDK
startup probe in the prepared task container before registering a provider run.
The probe creates and disposes a session without a prompt; network attempts are
rejected. A successful host `node --version` check alone does not establish
compatibility with a benchmark image.

`--retain-responses` explicitly enables private provider-body diagnostics for a
new run. Each forwarded response retains at most 2,000,000 exact body bytes in a
0600 host-only file, with its hash, received/captured sizes, HTTP status, and
transport completeness. Request bodies and authentication headers are not
included. These files contain local user/model data and remain outside candidate
mounts and Git. A truncated body is marked incomplete; it is never replayed as a
complete model response. Diagnostic storage failures are reported separately and
do not erase settled provider usage. Retention is disabled by default.
