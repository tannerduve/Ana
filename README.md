# Ana

Ana is a terminal agent harness written in Lean. Give it a task: a model proposes actions, and Lean admits and executes the application’s typed tools. Ana manages the model–tool loop, permissions, call limits, context and durable sessions for replay and recovery. Applications supply tools and instructions.

| Application | Tools |
| --- | --- |
| **Coding** | Inspect repositories, read/search/edit files, run permitted commands and tests, explain the work |
| **Inventory** | Query local stock, calculate replenishment totals and reserve stock with recoverable receipts; no file-editing or command tools |

Both use the same execution core and durable runner. Other applications can be compiled in through the [application interface](docs/Applications.md). Backends: direct Anthropic API, official Claude Code CLI or official Codex CLI.

**Working prototype for supervised Linux use.** [Durable-session validation](docs/reports/2026-11-11-durable-sessions.md) covers both applications; live task evaluations cover coding only. [eval/](eval/README.md) contains results, limitations, benchmark tooling and the Pi baseline.

## Getting started

### 1. Build on Linux

Requires **x86_64 Linux with glibc**; macOS and Windows hosts are unsupported. Install [elan](https://github.com/leanprover/elan#installation) and [rustup](https://rustup.rs/), with their `bin` directories on `PATH`. Lean and Rust toolchains are pinned; the first build downloads dependencies. Running Ana requires no Python. On Ubuntu/Debian:

```sh
sudo apt-get update
sudo apt-get install -y git build-essential libssl-dev curl bubblewrap

git clone https://github.com/tannerduve/Ana.git
cd Ana
lake build
.lake/build/bin/harness --help
```

Example configs require bubblewrap with user/PID/network namespaces and the [required features](runtime/README.md#files-and-processes). Unsupported sandboxes fail at startup. For a trusted local project, deliberately set `"executionProfile": "host"` in a copied config; commands then run with your OS user’s privileges.

### 2. Choose a model backend and sign in

| Backend | Config | Authentication |
| --- | --- | --- |
| Claude Code | [`examples/claude-code.json`](examples/claude-code.json) | Claude account: `claude auth login` |
| Codex | [`examples/codex.json`](examples/codex.json) | ChatGPT sign-in: `codex login` |
| Anthropic API | [`examples/config.json`](examples/config.json) | Real model ID and `ANTHROPIC_API_KEY` |

Install the official [Claude Code](https://code.claude.com/docs/en/setup) (`claude`) or [Codex](https://developers.openai.com/codex/cli/) (`codex`) CLI on the harness user’s `PATH`. The adapter targets Claude Code **2.1.322** and Codex **0.167.0** interfaces; older versions may lack required flags. Check versions and sign in outside Ana:

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

For CLI backends, sign-in stays in the unmodified official CLI. Ana extracts no OAuth tokens, requires no API key and forwards no API-key or provider-override environment variables. Account model access and subscription limits apply; Codex requires ChatGPT authentication.

Claude’s example uses `opus`; Codex’s `"model": "default"` uses the installed CLI’s default. Set `model` to another CLI-supported ID to choose a different model.

To use direct API access instead:

```sh
cp examples/config.json my-api-config.json
# Replace REPLACE_WITH_YOUR_MODEL_ID in my-api-config.json with your model ID.
export ANTHROPIC_API_KEY='your-api-key'
```

Omitting `modelBackend` selects `anthropic`. API billing is separate from CLI subscriptions. Keep credentials out of config files and Git.

### 3. Try a small task

From the repository root, create a disposable project and separate session:

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

Use `examples/codex.json` for Codex or your edited `my-api-config.json` for API access. Each `run` needs a new session directory. For a real repository, set its absolute path as `--workspace` and describe the change in `--task`.

File tools can edit the workspace. Example configs ask before commands; type `yes` to approve the exact command, or set `"commands": "deny"` to disable commands. [Capability policies](docs/Capabilities.md) further restrict direct file writes and exact process invocations. Ana runs until completion, a configured limit, cancellation or required recovery.

### 4. Continue, inspect or recover

```sh
# Add a task to a completed session:
.lake/build/bin/harness continue "$demo_root/session" \
  --task 'Explain which file you changed and why.'

# Inspect saved state, or replay it without model/tool execution:
.lake/build/bin/harness inspect "$demo_root/session"
.lake/build/bin/harness replay "$demo_root/session"

# Resume unfinished work after an interruption:
.lake/build/bin/harness resume "$demo_root/session"

# From another terminal, cancel the active turn (use the actual session path):
.lake/build/bin/harness cancel /absolute/path/to/session
```

Use `continue` for a new user turn and `resume` for unfinished work. Both retain the frozen backend/config and spent budgets. Uncertain mutations may need explicit resolution; read [recovery](runtime/README.md#persistence-and-recovery) first. Keep sessions outside the workspace. Add `--json` to `run`, `continue` or `resume` for structured events.

Try the engine without credentials using the scripted [inventory example](examples/inventory).

### How CLI backends work

Each invocation starts in a fresh private scratch directory, receives the complete harness-owned context through stdin and returns structured proposals. Native CLI conversations aren’t resumed.

- **Claude Code:** native file/command tools, MCP and customizations disabled; internal structured-output formatter allowed.
- **Codex:** read-only sandbox; shell execution, MCP, apps, plugins, hooks and other optional tools disabled. Native tool activity in the event stream is rejected.

For both coding and inventory, proposed application operations pass through Lean’s decoders, permissions, approvals, journal and recovery rules.

Official CLIs are trusted adapters: their authentication, internal inference, retries and schema generation are outside the Lean proofs. Compared with direct API mode:

- `maxModelAttempts` limits **CLI invocations**, not the exact number of upstream inference requests.
- `maxOutputTokens` is passed to the model only as an instruction. The adapter enforces the byte and elapsed-time limits.
- CLI progress is buffered until the invocation completes.
- Native token and cost settings, as well as performance, can differ from direct API mode.

Avoid `claude --bare`: it doesn’t load subscription authentication.

**Troubleshooting:**

- **The CLI cannot start.** Check its installation, version and `PATH`. Install the CLI outside the application workspace and session directory, and use an absolute directory entry in `PATH`. `TMPDIR` must also be outside those directories.
- **The CLI exits unsuccessfully.** Run its login and status commands, and confirm model access directly. The harness deliberately keeps CLI stderr out of the journal and diagnostics because it may contain account details.
- **The CLI rejects an option.** Update to a compatible CLI version.

CI tests use credential-free CLI stand-ins.

## Design

An application defines operations and a result type for each one. For example, an inventory lookup returns an optional item; warehouse totals return a list of summaries. A call and its possible observations define a polynomial functor. The harness adds model requests, approval, control checks, waits and termination:

$$
H_A(X) = \sum_{a : \mathsf{Action}_A} \bigl(\mathsf{Reply}_A(a) \to X\bigr),
\qquad \mathsf{step}_A : S_A \to H_A(S_A).
$$

`step` is a pure, total Lean function. It selects an action and provides a continuation from a typed reply to the next state. Lean IO performs the action. Model responses, tool results, time and cancellation enter as observations. The `harness` executable runs the same transitions the proofs describe.

This makes execution policy explicit and reusable. Changing the application changes the available tools, but the engine still owns admission, approvals, budgets, context and recovery.

## Implementation

| Component | Responsibility |
| --- | --- |
| [Application](Harness/Core/Application.lean) | Operation/result types, codecs, schemas, policy and recovery contracts |
| [Core](Harness/Core) | Mathlib `PFunctor`, serializable state, transitions, compaction and replay |
| [Persistence protocol](Harness/Core/Persistence.lean) | Proved intent/dispatch/completion ordering, executed by the runner |
| [Runner](Harness/Runner.lean) | Sessions, follow-up turns and interpretation of typed requests |
| [Lean adapters](Harness/Adapter) | Anthropic streaming, Claude Code/Codex CLI inference, filesystem access, process supervision, approvals and events |
| [Rust bindings](runtime/native/src) | Linux descriptors, process primitives, signals and SHA-256 through Lean's C ABI |

The core validates the entire proposed tool batch before any call runs, then executes calls sequentially with exact-action authorization and reserved budgets. Incomplete model responses cannot authorize execution. Coding edits require a matching file hash and one unambiguous text match.

[Scoped permissions](docs/Capabilities.md) restrict file-tool paths, exact commands, artifacts and application resources. Additional ceilings only narrow authority; approval cannot override them. Lean proves the containment checker sound and connects permissions to dispatch, including after recovery.

Sessions store data, not continuation closures. Replay rebuilds the continuations through `step` without contacting the model or running tools. Follow-up turns keep permissions, spent budgets and operation identities. Compaction keeps the raw transcript and installs a summary plus a valid recent suffix. Lost outcomes stay explicit, and uncertain mutations require recovery before another turn can run. The [runtime reference](runtime/README.md) documents limits, storage and recovery.

## Verification and testing

[Lean proofs](Harness/Proofs) cover permissions, single-use approvals, cumulative budgets, unique intent IDs across recovery and follow-ups, valid histories and bounded execution per turn.

The persistence protocol requires matching durable acknowledgments before dispatch or advancement. [Application laws](docs/ApplicationContracts.md) establish valid tool decoding, codec round trips and faithful presentation of observations. Physical durability, the truth of observations and process cleanup remain obligations of the adapters and the OS.

Deterministic and generated tests exercise real files, processes, streaming and storage faults. A [combined CLI gate](Tests/DurableSessions.lean) runs both applications through three turns, repeated compaction, a restart and a committed mutation whose reply is lost. The validation report above includes journal performance and remaining limits. [CI](.github/workflows/ci.yml) lists the checks.

Task quality is measured separately. The [latest coding evaluation](eval/reports/2026-11-11-durable-sessions.md) includes independent reviews of patches and summaries. It does not establish general production readiness, parity with Pi or live task quality for inventory. [Safety and trust assumptions](docs/Safety.md) distinguishes proofs, tests and deployment obligations.
