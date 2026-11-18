# Lean harness

An agent harness written in Lean. It runs the model–tool loop, enforces permissions and call limits, manages context, and saves sessions for replay and recovery. Applications supply typed tools and instructions.

| Application | Tools |
| --- | --- |
| **Coding** | Inspect repositories, edit files, search, run commands and tests |
| **Inventory** | Query local stock, calculate replenishment totals and reserve stock with recoverable receipts |

Both use the same execution core and durable runner. Choose direct Anthropic API access, the official Claude Code CLI, or the official Codex CLI as the model backend. The inventory application has no file-editing or command tools. Other applications can be compiled in through the [application interface](docs/Applications.md).

**Status: working prototype for supervised Linux use.** The [durable-session validation](docs/reports/2026-11-11-durable-sessions.md) covers both applications. Live task evaluations cover coding; see [results and limitations](eval/README.md).

## Design

An application defines operations and a result type for each operation. For example, inventory lookup returns an optional item; warehouse totals returns a list of summaries. A call and its possible observations define a polynomial functor. The harness adds model requests, approval, control checks, waits and termination:

$$
H_A(X) = \sum_{a : \mathsf{Action}_A} \bigl(\mathsf{Reply}_A(a) \to X\bigr),
\qquad \mathsf{step}_A : S_A \to H_A(S_A).
$$

`step` is a pure, total Lean function: it selects an action and provides a continuation from a typed reply to the next state. Lean IO performs the action. Model responses, tool results, time and cancellation enter through observations. The CLI executes the same transition definitions the proofs describe.

This makes execution policy explicit and reusable. Changing the application changes the available tools; the engine still owns admission, approvals, budgets, context and recovery.

## Implementation

| Component | Responsibility |
| --- | --- |
| [Application](Harness/Core/Application.lean) | Operation/result types, codecs, schemas, policy and recovery contracts |
| [Core](Harness/Core) | Mathlib `PFunctor`, serializable state, transitions, compaction and replay |
| [Persistence protocol](Harness/Core/Persistence.lean) | Proved intent/dispatch/completion ordering, executed by the runner |
| [Runner](Harness/Runner.lean) | Sessions, follow-up turns and interpretation of typed requests |
| [Lean adapters](Harness/Adapter) | Anthropic streaming, Claude Code/Codex CLI inference, filesystem access, process supervision, approvals and events |
| [Rust bindings](runtime/native/src) | Linux descriptors, process primitives, signals and SHA-256 through Lean's C ABI |

The core validates an entire proposed tool batch before any call runs. Calls execute sequentially, with exact-action authorization and reserved budgets. The coding application's edit tool requires a matching file hash and one unambiguous text match. An incomplete model response cannot authorize execution.

[Scoped permissions](docs/Capabilities.md) can restrict file-tool paths, exact commands, artifacts and application resources. Additional ceilings only narrow authority; approval cannot override them. Lean proves the containment checker sound and connects those permissions to dispatch, including after recovery.

Sessions store data, not continuation closures. Replay reconstructs continuations through `step` without contacting the model or executing tools. Follow-ups retain permissions, spent budgets and operation identities. Compaction retains the raw transcript and installs a summary plus a valid recent suffix. Lost outcomes remain explicit; uncertain mutations require recovery before another turn. See the [runtime reference](runtime/README.md).

The executable needs no Python runtime. Benchmark tooling and the Pi baseline live in [eval/](eval/README.md).

## Getting started

The harness is a terminal agent: give it a project directory and a task, and it can read files, propose edits, run permitted commands and explain its work. The model backend supplies proposals; Lean admits and executes application tools.

### 1. Build on Linux

The supported host is **x86_64 Linux with glibc**. Install [elan](https://github.com/leanprover/elan#installation) and [rustup](https://rustup.rs/), and ensure their `bin` directories are on `PATH`. The repository pins its Lean and Rust toolchains; the first build downloads dependencies.

On Ubuntu/Debian, install the system dependencies:

```sh
sudo apt-get update
sudo apt-get install -y git build-essential libssl-dev curl bubblewrap

git clone https://github.com/tannerduve/lean-harness.git
cd lean-harness
lake build
.lake/build/bin/harness --help
```

The example configs use bubblewrap. Your host must allow its user/PID/network namespaces and provide the required bubblewrap features; see [host requirements](runtime/README.md#files-and-processes). An unsupported sandbox fails at startup. For a trusted local project, you can deliberately select `"executionProfile": "host"` in a copied config; commands then have your OS user's privileges. macOS and Windows are not supported harness hosts yet. Python is not required to run the harness.

### 2. Choose a model backend and sign in

| Backend | Config | Authentication |
| --- | --- | --- |
| Claude Code | [`examples/claude-code.json`](examples/claude-code.json) | Install the official `claude` CLI and run `claude auth login` with your Claude account |
| Codex | [`examples/codex.json`](examples/codex.json) | Install the official `codex` CLI and run `codex login`, choosing ChatGPT sign-in |
| Anthropic API | [`examples/config.json`](examples/config.json) | Set a real model ID and supply `ANTHROPIC_API_KEY` |

Install the official CLIs using the [Claude Code setup guide](https://code.claude.com/docs/en/setup) or [Codex installation guide](https://developers.openai.com/codex/cli/). They must be on the same user's `PATH` as the harness. The adapter targets the interfaces in Claude Code **2.1.322** and Codex **0.167.0**; older releases may lack required flags. Check the installed version and login outside the harness:

```sh
# Claude subscription backend
claude --version
claude auth login
claude auth status

# Or ChatGPT/Codex subscription backend
codex --version
codex login
codex login status
```

Sign-in stays in the unmodified official CLI. The harness does not extract OAuth tokens or require an API key for these two backends. Account/model access and subscription limits still apply. Claude's example selects `opus`; Codex's `"model": "default"` leaves selection to the installed CLI. Set `model` to a CLI-supported model ID to choose another. The Codex adapter requires ChatGPT authentication. API-key and provider-override environment variables are not forwarded to either CLI backend.

For direct API access instead:

```sh
cp examples/config.json my-api-config.json
# Edit my-api-config.json: replace REPLACE_WITH_YOUR_MODEL_ID with your model ID.
export ANTHROPIC_API_KEY='your-api-key'
```

Omitting `modelBackend` selects the existing `anthropic` API backend. Its API billing is distinct from signing into a subscription through a CLI. Keep credentials out of config files and Git.

### 3. Try a small task

From the harness repository root, this creates a disposable workspace and a separate session directory. Use your chosen config:

```sh
demo_root="$(mktemp -d)"
mkdir "$demo_root/project"
printf '%s\n' '2 + 2 = 5' > "$demo_root/project/notes.txt"

# Claude Code / Opus:
.lake/build/bin/harness run --application coding \
  --workspace "$demo_root/project" --config examples/claude-code.json \
  --task 'Read notes.txt, correct the arithmetic, and explain the change.' \
  --session "$demo_root/session"

cat "$demo_root/project/notes.txt"
```

For Codex, replace `examples/claude-code.json` with `examples/codex.json`. For API access, use your edited `my-api-config.json`. Each `run` needs a new session directory. To work on a real repository, supply its absolute path as `--workspace` and describe the desired change in `--task`.

File tools can edit the selected workspace. The example configs ask before running commands; approve an exact command by typing `yes` when prompted. `commands: "deny"` disables commands. [Capability policies](docs/Capabilities.md) can restrict direct file writes and exact process invocations further. The harness keeps working until it finishes, hits a configured limit, is cancelled, or requires recovery.

### 4. Continue, inspect or recover

```sh
# Add a task to a completed session:
.lake/build/bin/harness continue "$demo_root/session" \
  --task 'Explain which file you changed and why.'

# Inspect saved state or replay it without model/tool execution:
.lake/build/bin/harness inspect "$demo_root/session"
.lake/build/bin/harness replay "$demo_root/session"

# Resume unfinished work after an interruption:
.lake/build/bin/harness resume "$demo_root/session"

# In another terminal, cancel the active turn using its actual session path:
.lake/build/bin/harness cancel /absolute/path/to/session
```

Use `continue` for a new user turn and `resume` for unfinished work. Both retain the frozen backend/config and spent budgets. Uncertain mutations may require explicit resolution; read [recovery](runtime/README.md#persistence-and-recovery) before resolving them. Sessions must be outside the workspace. Add `--json` to `run`, `continue` or `resume` for structured events.

### How CLI backends work

Each CLI invocation starts in a fresh private scratch directory, receives the complete harness-owned context through stdin, and returns structured proposals. It does not resume a native CLI conversation. Claude Code's native file/command tools, MCP and customizations are disabled; its internal structured-output formatter is allowed. Codex uses a read-only sandbox with shell execution, MCP, apps, plugins, hooks and other optional tools disabled; native tool activity in its event stream is rejected. Proposed application operations still go through Lean's existing decoders, permissions, approvals, journal and recovery rules. This works for inventory as well as coding.

The official CLIs remain trusted runtime adapters. Their authentication, internal inference, retries and schema generation are outside the Lean proofs. With CLI backends, `maxModelAttempts` limits **CLI invocations**, not the exact number of upstream inference requests; `maxOutputTokens` is supplied as an instruction, while byte and elapsed-time limits are enforced by the adapter. CLI progress is buffered until completion. Native token/cost settings and performance can differ from direct API mode. Do not use `claude --bare` for this adapter: bare mode does not load subscription authentication.

If a CLI cannot start, check its installation, version and `PATH`. Install it outside the application workspace and session, using an absolute `PATH` entry; `TMPDIR` must also be outside those roots. If it exits unsuccessfully, run its login/status commands and confirm model access directly. CLI stderr is deliberately not copied into the journal or diagnostics because it may contain account details. Update to a compatible CLI if an option is rejected. CI tests use credential-free CLI stand-ins.

The [inventory example](examples/inventory) also provides a credential-free scripted run for trying the engine before signing in. The full [runtime reference](runtime/README.md) documents limits, storage and recovery.

## Verification and testing

[Lean proofs](Harness/Proofs) cover permissions, single-use approvals, cumulative budgets, unique intent IDs across recovery and follow-ups, valid histories and bounded execution per turn. The persistence protocol requires matching durable acknowledgments before dispatch or advancement. [Application laws](docs/ApplicationContracts.md) establish valid tool decoding, codec round trips and faithful presentation of observations. Physical durability, observation truth and process cleanup remain adapter and OS obligations.

Deterministic and generated tests exercise real files, processes, streaming and storage faults. A [combined CLI gate](Tests/DurableSessions.lean) runs both applications through three turns, repeated compaction, restart and a committed mutation whose reply is lost. The [validation report](docs/reports/2026-11-11-durable-sessions.md) includes journal performance and remaining limits; [CI](.github/workflows/ci.yml) lists the checks.

Task quality requires separate measurement. The [latest coding evaluation](eval/reports/2026-11-11-durable-sessions.md) includes independent patch and summary reviews. It does not establish general production readiness, Pi parity or live inventory task quality. [Safety and trust assumptions](docs/Safety.md) distinguish proofs, tests and deployment obligations.
