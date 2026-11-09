# Lean harness

A command-line coding agent with an execution loop written in Lean. It calls the Anthropic Messages API to inspect repositories, edit files, and run commands. A configuration file selects the model, instructions, limits, and command permissions.

## Design

The agent loop is defined by a pure step function. Given the current state, it returns an action and a continuation: a function from that action's possible replies to the next state. The runner performs the action and supplies a typed observation to the continuation. Model responses, tool results, time, and cancellation enter through these observations. Finishing has no reply and ends the loop.

For a state type $S$, this is a coalgebra of a polynomial functor:

$$
F(X) = \sum_{a : \mathsf{Action}} \bigl(\mathsf{Reply}(a) \to X\bigr),
\qquad \mathsf{step} : S \to F(S).
$$

The reply type depends on the action. Lean checks these types and the proofs about the same transition definitions the CLI executes.

## Implementation

The [core](Harness/Core) defines the functor with Mathlib's `PFunctor` as `HarnessF`:

```lean
step : State → HarnessF State
```

`step` is pure and total. The effect signature is generic over a `ToolAPI`; the current `step` uses the coding tool set.

`State` is JSON-serializable: phase, history, frozen config, counters, call IDs, and an optional exact-call grant. `step` reconstructs continuations from this data; closures are never persisted.

Before accepting a model response, the [core](Harness/Core/ModelResponse.lean) checks that its tool calls and text match the retained content blocks. It validates the whole tool batch before dispatch: schemas, path syntax, bounds, and duplicate IDs. Calls run sequentially, with budget reserved before dispatch. An edit requires a matching file SHA-256 and exactly one occurrence of the text to replace.

| File | Responsibility |
|---|---|
| [Provider](Harness/Adapter/ProviderIO.lean) | Lean request encoding and response handling; curl supplies HTTPS |
| [Runner](Harness/Runner.lean) | Carries out each core request and records its result |
| [Lean IO](Harness/Adapter) | Files, supervised processes, approvals, and durable journal writes |
| [Rust native bindings](runtime/native/src) | Linux file descriptors, process primitives, signals, and SHA-256 through a direct Lean C ABI |

The runner writes an intent record before each effect and a completion record before the core consumes the reply. Replay feeds recorded replies through `step` without calling the model or tools. IO functions perform one operation; permission, retry, and budget decisions stay in the core. The native library is Rust, with no handwritten C shim. Python is used only for tests and evaluation.

## Run it

Requires x86_64 Linux/glibc, elan, rustup, a C compiler/linker for Lean, OpenSSL development files, and `curl` (`build-essential libssl-dev curl` on Ubuntu). Put both `~/.elan/bin` and `~/.cargo/bin` on `PATH`. [rust-toolchain.toml](rust-toolchain.toml) pins Rust 1.97.1; Lake builds the native static library with the checked-in Cargo lockfile.

```sh
lake build
cp examples/config.json config.json   # set "model"
export ANTHROPIC_API_KEY=...
.lake/build/bin/harness run --workspace /path/to/repo --config config.json \
  --task 'Fix the parser bug' --session /path/to/session
```

`inspect SESSION`, `replay SESSION`, `resume SESSION`, and `cancel SESSION` operate on an existing session. Add `--json` to print JSONL events. See the [runtime reference](runtime/README.md) for details.

Keep session storage outside the workspace. The default is `~/.local/state/lean-harness/sessions` (or `$XDG_STATE_HOME/lean-harness/sessions`).

## Verification and testing

**Formal verification.** [Lean proofs](Harness/Proofs) cover call limits, authorization of emitted tools, grants bound to exact calls, frozen configuration, rejection of inconsistent model responses, and stopping after consumed cancellation. They describe the executable core. The replay theorem currently establishes determinism.

**Testing.** [Plausible](Tests/Properties.lean) checks 900 generated protocol cases; another [100 generated cases](Tests/RuntimeProperties.lean) exercise real files and journals. Integration and fault tests cover HTTP, process cleanup, path escapes, stale edits, failed writes, and crashes around persistence boundaries. [Native ABI tests](Tests/native_abi.py) exercise actual Lean/Rust values and descriptor ownership. CI also rejects proof placeholders and checks theorem axioms.

IO, Rust's unsafe FFI bindings, and the OS remain outside the proofs. Neither proofs nor passing tests establish that the model solves a task correctly. The [safety specification](docs/Safety.md) records the guarantees, assumptions, and remaining work.

## Status and limits

A [live Opus 5.5 run through the Lean runtime and Rust bindings](eval/reports/2026-11-09-rust-native.md) fixed a parser bug and passed the independent checker. Broader reliability and parity remain unmeasured. See the [development report](eval/reports/2026-11-08-development.md).

There is no compaction: runs stop at the context byte limit. Resume refuses an intent without a completion because the operation may already have had effects.

There is no OS sandbox. Process calls ask for approval by default. Use an isolated environment for untrusted work.
