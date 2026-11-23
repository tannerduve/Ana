# Ana in Matrix

Matrix can select Ana for an author, selector, reviewer or repair role. Pi/Kimi
remains the default. Matrix owns prompts, candidate capture, independent builds,
review validation and acceptance; Ana owns the role's model/tool loop and durable
journal. A completed Ana turn does not establish that a candidate is accepted.

Build Ana with `lake build harness`, then install the resulting
`.lake/build/bin/harness` as a regular executable outside the Matrix and agent
checkouts. Matrix's operator settings require its absolute path and SHA-256.
Changing the executable requires a new pin and a fresh role session.

See [Matrix's Linux setup and operator settings](https://github.com/tannerduve/aleph-matrix/blob/main/deploy/local/README.md)
for installation and commands. The coordinated agent release must include the
managed-session factory and protected Ana tool helper. Older releases fail
preflight rather than silently selecting another harness.

Supported model transports are the Anthropic API and the official Claude Code
and Codex CLIs. CLI profiles use the CLI's existing sign-in; OAuth tokens stay in
the official client's storage. These profiles clear ambient API-key overrides;
direct API profiles use the operator's selected environment variable.
A subscription must include access to the selected
model. Ana has no Kimi transport in this integration. Selecting Ana/Claude for an
author while retaining Pi/Kimi for other roles does not establish Pi parity.

The compiled `matrix` application adds `lake_build`, `submit_selection`,
`submit_review` and `submit_environment_repair` to the coding operations. The
frozen role allows only its configured tools. Skills are read under `@skills`,
temporary projects under `@scratch`, and declared proof obligations under
`@goals`. Commands use the bubblewrap profile; workspace intent and resource
mount permissions apply inside the process sandbox. The supported checkout has
local `.git` directory metadata; linked worktrees are refused.
Use a canonical checkout path outside reserved system roots such as `/dev`;
placing `TMPDIR` under `/dev/shm` will be refused by the sandbox.

Matrix binds the journal to its execution, attempt, agent, turn, request,
checkout identity, executable and configuration. A private live-controller key
authorizes reopening it. Restart is allowed only within that same turn and its
original outer deadline. A successor receives new identities and a new journal;
an old journal may be retained as context.

Build intents record the admitted source digest before dispatch and the prepared
upload digest, targets and scope immediately before the pinned client submits.
Acknowledged backend IDs are retained for status and cancellation. An ambiguous
initial submission with no ID stays unresolved: restarting never repeats it.
Structured submissions preserve the exact payload for the existing controller
validators and seal further tool admission. Mixed submission batches are refused
before their first effect.

The JSONL stream is bounded progress. After the process stops, Matrix uses Ana's
validated journal prefix to recover semantic events, including output loss and
exit 74. Cancellation first closes effect admission, requests targeted native
cancellation, then independently settles the supervised process tree and known
builds. Unresolved effects remain evidence for the controller's next decision.

Transcripts retain the journal, operation receipts, disposition and bounded
artifacts. Available provider usage is reported with explicit unknowns for
missing cache categories, cost and upstream request counts. Model attempts count
Ana invocations; an official CLI may make several upstream requests internally.
