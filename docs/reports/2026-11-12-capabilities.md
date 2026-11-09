# Scoped capabilities: implementation and validation

November 12, 2026. Sessions can restrict file paths, exact process invocations,
artifact retrieval and application resources. Restrictions are hard ceilings:
approvals cannot override them, and recovery retains them. Existing defaults
remain unchanged until a capability policy is configured.

| Property | Evidence |
| --- | --- |
| Adding a ceiling cannot increase authority | Lean containment proof for policy intersection |
| An accepted containment check is sound | Proof about the executable `checkContained` function |
| Dispatched tools satisfy the frozen ceilings | Theorems about `step`, reachable states and accepted replay |
| Installed tools declare the required accesses | Coding and inventory classifiers proved against explicit operation requirements |
| Denied operations do not reach their adapters | Real CLI tests, including edit preparation, exact command matching and inventory mutations |

The checker is conservative: `not_established` is not an escalation witness.
These permissions govern declared tool accesses. They do not confine an approved
process's downstream effects or establish information-flow security. The
[policy guide](../Capabilities.md) explains configuration and these boundaries.

## Local checks

| Check | Result |
| --- | --- |
| Pinned Lean build and executable gates | Passed |
| Selected declaration and source-boundary audit | Passed; 223 declarations, including 35 added for capabilities |
| Plausible provider/core and capability checks | 1,500 generated cases passed, plus deterministic fixtures |
| Stateful IO checks | 100 generated cases, 200 sequences of 30 operations, and 40 recovery sequences of 12 turns passed |
| Python boundary tests | 161 existing tests and 13 new capability CLI tests passed |

The journal fault gate's first attempt could not find `rustc` in its subprocess
environment. It passed after correcting the test PATH; no product change was
needed. The [validation record](2026-11-12-capabilities.json) records both attempts
and binds the tested sources, binaries and logs.

All model responses were scripted or served by local test fixtures. No paid
provider calls or new task-quality evaluations were run for this change.
