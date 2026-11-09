# Self-authored coding corpus

This is a small development corpus, not evidence of general reliability or Pi
parity. It contains **12 development tasks and 4 reserved tasks**: Python API/CLI
changes, repository navigation, JavaScript parsing and collection bugs, Rust
byte/path handling, and Lean proof repair. Tasks require no downloaded packages.

The reserved tasks have separate IDs and reporting. Their fixtures and reference
solutions are checked mechanically, but their cases must not inform prompt or
tool tuning before the first comparison. “Reserved” does not establish that an
underlying programming pattern is absent from model training.

## Runner contract

`manifest.json` is versioned and contains fixture paths, editable/immutable file
lists, requirements, checker limits, and SHA-256 hashes of every fixture, case
file, and reference file. Paths are relative to this directory. Copy **only** a
task's `fixture` directory into a fresh agent workspace. The task is its README.
Do not mount this directory, case files, checkers, references, solution history,
or the parent repository in the agent environment. Initialize a fresh repository
if the coding agent needs git. Check final source independently after the agent
process has stopped.

```sh
python3 eval/corpus/check.py dev01-inventory-cli /path/to/candidate
```

The checker prints one JSON result. Exit 0 means the task check passed; 1 means
candidate failure, including modified immutable files; 2 means infrastructure
failure. Record all three outcomes in evaluation denominators. Tool paths come
from `LEAN_BIN`, `RUSTC_BIN`, `NODE_BIN`, or `PATH`. Use actual pinned binaries,
not a rustup/elan shim with an unavailable home directory. Development validation
used Python 3.12.3, Node 24.16.0, Rust 1.97.1 and Lean 4.33.1. Lean fixtures include
their toolchain pin and use only its standard library.

Only allowlisted source files enter the checker's temporary candidate directory;
agent-produced binaries and object files are ignored. Immutable README, public
tests, facades and Lean definitions/specifications must match their hashes.
Expected answers stay in the parent checker, outside the candidate process.
Python and JavaScript workers report values, exceptions, mutation and aliasing;
Rust probes report bytes/results; Lean checks compile the fixed specification
and inspect the theorem's transitive axiom report. These checks prevent ordinary
test deletion, statement weakening and checker bypasses. They are **not** a
sandbox against intentionally malicious candidate code: the enclosing runner
must supply process/filesystem isolation. Never give checker processes API keys.

The checker's per-process timeouts fit within each task's 120-second external
deadline. The enclosing runner should also bound process groups, output, memory
and filesystem use. A checker timeout is a recorded failure, not a discarded run.

## Validation and continuation tasks

```sh
python3 eval/corpus/validate.py --output /tmp/corpus-validation.json
python3 eval/corpus/test_checkers.py
```

Validation copies a fixture, checks that its baseline fails, overlays only its
reference implementation, then checks that the reference passes. It never uses
a model. The checked-in `validation.json` records this evidence separately from
agent results. `test_checkers.py` supplies negative controls for changed tests,
README changes, source symlinks, input mutation, weakened theorems, proof holes,
and unexpected import files. Source/reference hashes identify this corpus version;
changing a task requires regenerating its hashes and validating it again.

`reserved01-atomic-settings` and `reserved02-js-ledger` are candidates for
continuation testing. Their `sustained_acceptance` requires both a successful
compaction and a durable restart, in addition to task correctness. An evaluation
must configure a deliberate context threshold/checkpoint, preserve the journal,
and independently verify those events, valid resumed histories, and accounted
attempts. These small tasks may finish without either event, so a functional pass
alone is **not** a sustained-session pass. Report that gate as not exercised when
the required events do not occur.
