# Lean harness

An agent harness written in Lean. It runs the model–tool loop, enforces permissions and call limits, manages context, and saves sessions for replay and recovery. Applications supply typed tools and instructions.

| Application | Tools |
| --- | --- |
| **Coding** | Inspect repositories, edit files, search, run commands and tests |
| **Inventory** | Query local stock, calculate replenishment totals and reserve stock with recoverable receipts |

Both use the same execution core, Anthropic adapter and durable runner. The inventory application has no file-editing or command tools. Other applications can be compiled in through the [application interface](docs/Applications.md).

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
| [Lean adapters](Harness/Adapter) | Anthropic streaming, filesystem access, process supervision, approvals and events |
| [Rust bindings](runtime/native/src) | Linux descriptors, process primitives, signals and SHA-256 through Lean's C ABI |

The core validates an entire proposed tool batch before any call runs. Calls execute sequentially, with exact-action authorization and reserved budgets. The coding application's edit tool requires a matching file hash and one unambiguous text match. An incomplete model response cannot authorize execution.

[Scoped permissions](docs/Capabilities.md) can restrict file-tool paths, exact commands, artifacts and application resources. Additional ceilings only narrow authority; approval cannot override them. Lean proves the containment checker sound and connects those permissions to dispatch, including after recovery.

Sessions store data, not continuation closures. Replay reconstructs continuations through `step` without contacting the model or executing tools. Follow-ups retain permissions, spent budgets and operation identities. Compaction retains the raw transcript and installs a summary plus a valid recent suffix. Lost outcomes remain explicit; uncertain mutations require recovery before another turn. See the [runtime reference](runtime/README.md).

The executable needs no Python runtime. Benchmark tooling and the Pi baseline live in [eval/](eval/README.md).

## Run it

Requires x86_64 Linux/glibc, elan, rustup, a C compiler/linker, OpenSSL development files and `curl`. The toolchains are pinned. The coding example uses bubblewrap; check its [host requirements](runtime/README.md#files-and-processes).

```sh
lake build
cp examples/config.json config.json   # set "model"
export ANTHROPIC_API_KEY=...
.lake/build/bin/harness run --application coding \
  --workspace /path/to/repo --config config.json \
  --task 'Fix the parser bug' --session /path/to/session
```

Continue a completed or settled cancelled turn with:

```sh
.lake/build/bin/harness continue /path/to/session --task 'Now add a regression test'
```

Inventory accepts a bounded JSON dataset instead of a workspace. Its [example](examples/inventory) includes a credential-free scripted run. `resume` recovers unfinished work; `continue` adds a user turn. `inspect`, `replay`, `cancel` and `resolve` also operate on saved sessions; `--json` emits structured events with turn and operation IDs.

## Verification and testing

[Lean proofs](Harness/Proofs) cover permissions, single-use approvals, cumulative budgets, unique intent IDs across recovery and follow-ups, valid histories and bounded execution per turn. The persistence protocol requires matching durable acknowledgments before dispatch or advancement. [Application laws](docs/ApplicationContracts.md) establish valid tool decoding, codec round trips and faithful presentation of observations. Physical durability, observation truth and process cleanup remain adapter and OS obligations.

Deterministic and generated tests exercise real files, processes, streaming and storage faults. A [combined CLI gate](Tests/DurableSessions.lean) runs both applications through three turns, repeated compaction, restart and a committed mutation whose reply is lost. The [validation report](docs/reports/2026-11-11-durable-sessions.md) includes journal performance and remaining limits; [CI](.github/workflows/ci.yml) lists the checks.

Task quality requires separate measurement. The [latest coding evaluation](eval/reports/2026-11-11-durable-sessions.md) includes independent patch and summary reviews. It does not establish general production readiness, Pi parity or live inventory task quality. [Safety and trust assumptions](docs/Safety.md) distinguish proofs, tests and deployment obligations.
