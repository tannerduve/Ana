# Scoped tool permissions

Capability policies limit which resources the installed tools may access. They
add a hard ceiling to the existing allow/ask/deny policy. Approval cannot override
that ceiling. Model tool arguments cannot grant or change permissions; startup
configuration and session storage retain their existing trust assumptions.

For example, a documentation task can read `docs/`, write `drafts/`, and run no
commands. An inventory task can look up selected SKUs without reserving stock.

## Configure a session

Add `capabilityPolicy` to the normal configuration:

```json
{
  "model": "YOUR_MODEL_ID",
  "commands": "deny",
  "capabilityPolicy": [[
    {"kind": "read", "scope": {"kind": "tree", "path": "docs"}},
    {"kind": "read", "scope": {"kind": "tree", "path": "drafts"}},
    {"kind": "write", "scope": {"kind": "tree", "path": "drafts"}}
  ]]
}
```

Each inner list offers alternatives. **Every inner list must permit every access
required by the operation.** Adding another list therefore restricts the policy.
`[]` adds no resource restriction, preserving the existing default behavior;
`[[]]` denies all tools. A configured policy with no process grant denies commands
even when `commands` is `allow` or a matching approval exists.

Paths are relative to the workspace. Exact scopes cover one path; tree scopes
cover that path and its descendants. Matching uses path components: `docs` never
matches `docs-private`. Policy matching normalizes harmless `.` and repeated separators;
absolute paths, `..` and NUL are rejected. Filesystem adapters separately reject
symlink traversal and may reject path spellings accepted by lexical scope matching.
Scopes authorize path names, not file-object provenance. In the host profile,
a preexisting hard link under an allowed name can expose bytes also reachable
through a denied name. Workspace preparation must control such aliases when that
separation matters; the bubblewrap startup scan already rejects hard links.

| Grant | Meaning |
| --- | --- |
| `{"kind":"read","scope":{"kind":"exact","path":"README.md"}}` | Read that file, including full-file identity and metadata |
| `{"kind":"write","scope":{"kind":"tree","path":"drafts"}}` | Direct tool writes beneath `drafts` |
| `{"kind":"process","argv":["pytest","-q"],"cwd":"tests"}` | That exact argument array and normalized working directory |
| `{"kind":"processes"}` | Any admitted process invocation |
| `{"kind":"artifact","id":"ARTIFACT_ID"}` | Read bytes from that registered artifact |
| `{"kind":"artifacts"}` | Read any registered artifact |
| `{"kind":"resource","application":"inventory","action":"lookup","scope":{"kind":"exact","value":"N-CABLE"}}` | Look up that inventory SKU |
| `{"kind":"everything"}` | Any declared access; other policy layers and approval rules still apply |

An edit requires both read and write authority because it inspects the preimage.
Create/overwrite requires write authority. List and search require a read-tree
grant covering their entire requested subtree; they do not return a silently
filtered view. Use a narrower path when a broad query is denied.

Inventory rights are separate: `lookup` uses a SKU, `reserve` uses a SKU,
`low_stock` uses a warehouse, and `warehouse_totals` requires scope `{"kind":"all"}`.
A reservation needs both `lookup` and `reserve` rights for its SKU because its
receipt reveals stock values. An `all` resource scope covers all resources for
that exact application/action pair. Warehouse-query permission does not grant
per-SKU lookup, and SKU permission does not grant warehouse aggregates.

Unknown fields and tags, invalid scopes and oversized policies fail validation.
Policies allow at most 32 layers and 1,024 grants in total. The parser also bounds
path, argument and resource-identity lengths. Policies remain frozen across
resume, recovery and follow-up turns.

## Restrict and check policies

These commands operate on JSON policy files and make no model calls:

```sh
# PARENT and CHILD contain complete policies: lists of grant lists.
harness policy check parent.json child.json

# LIMIT contains one grant list. Output retains every parent ceiling.
harness policy restrict parent.json limit.json > child.json

# Apply an additional ceiling when starting a session from a normal config.
harness run --application coding --workspace /path/to/repo \
  --config config.json --restrict-capabilities limit.json --task 'Write the guide'
```

Policy/restriction files must be regular, singly-linked files of at most 1 MiB;
the final path component cannot be a symlink. `check` returns JSON
`{"status":"contained"}` with exit 0 when its proved checker establishes
containment. Otherwise it returns `{"status":"not_established"}` with exit 3. That result is
not a counterexample: the finite checker is sound but deliberately incomplete.
For example, it may fail to recognize containment that requires reasoning about
the intersection of several different layers together. It uses no SMT solver.

Restriction takes effect only for a new session. The helper can construct a
narrower policy for an application or a future child agent; it does not launch a
child agent or change the permissions of an existing session.

## Guarantees and boundaries

Lean proves the checker's soundness, that intersecting restrictions cannot
increase authority, and that each emitted tool satisfies the frozen policy.
The dispatch result also applies after accepted recovery and follow-up records.
Both installed applications prove their operation-to-access classifications
against explicit disclosure/mutation requirements. Full authorization attenuation
also requires the application's other policy decisions to be independent of the
capability field; both installed applications prove this condition.

These are **tool-invocation permissions**, not information-flow guarantees or
an OS sandbox configuration. An authorized process can read or write whatever its
execution profile exposes, including the wider workspace. File-tool scopes do not
restrict Python imported by `pytest`, shell descendants, or other subprocess
effects. Deny processes when relying solely on file-tool scopes. No network,
credential, executable-integrity or cross-agent communication policy is added.

Artifact permissions govern byte retrieval; catalog metadata remains visible in
context. Inventory permissions govern domain queries and mutations; the trusted
adapter still reads its ledger, and trusted session inspection can display the
full saved configuration. The classifiers' agreement with physical IO remains an
adapter contract, exercised by tests. See [Safety](Safety.md).
