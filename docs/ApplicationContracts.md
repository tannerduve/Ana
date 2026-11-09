# Application contracts

An application is compiled into the executable. Its operation family, dependent result family,
codecs, schemas, permissions, rendering and recovery rules are trusted application code; model
arguments cannot replace them. `ApplicationLaws` states the pure obligations, which both supplied
applications prove. The IO interpreter has separate obligations.

`requiredCapabilities` declares every resource needed by an operation, including
preparation and result disclosures. Empty declarations are denied. The installed
applications prove their classifications against explicit operation-level demand
relations in `ApplicationCapabilities.lean`. The shared dispatch theorem then
requires all those demands to satisfy the frozen [capability policy](Capabilities.md).
This proves consistency of the pure classification and authorization; the adapter
must still implement the declared access rather than perform undeclared effects.

## Pure laws

`ValidOperation` and `ValidResult` describe domain fields, independently of JSON codecs. Coding
validity checks lexical paths, argument bounds and result metadata. Inventory validity checks item
bounds, exact operation correlations, page sizes and continuations, unique rows, warehouse totals,
and reservation identity and arithmetic. These are admissibility properties. A structurally valid
stock count does not establish that it equals the current stock.

The concrete contracts prove:

- A successfully decoded model operation is valid. The real whole-batch validator, pending queue,
  ordinary transitions and administrative replay preserve that validity, including follow-up turns.
- Storage operation codecs round trip. Dependent result codecs round trip for valid values. Result
  encodings are non-null, so an optional retained partial value cannot collapse into `none`.
- Complete tool observations round trip through the action-indexed completion codec used by replay.
- Coding renders every field of its result unchanged. Inventory renders its canonical tagged result
  with no process-exit, file-hash or artifact claim. The shared transition's actual continuation
  produces the specified model-visible blocks, including error flags, artifact-metadata rejection,
  timeout normalization, ordered skipped-call errors, policy denial, approval denial and cancellation.
  Uncertain/interrupted effects do not acquire an invented completion result.

These are JSON-value laws. They do not prove that arbitrary JSON text round trips byte-for-byte,
that summaries preserve meaning, or that the model actually uses the supplied history. Omitted
model-argument defaults are normalized. Arbitrary typed values need not satisfy domain validity:
for example, a lookup result with the wrong SKU or a receipt with invalid arithmetic is rejected.

Provider schemas document the input language but are not an equivalent second validator. Some
field restrictions and correlations are enforced only by the decoder. No theorem equates schema
acceptance with decoder acceptance. Likewise, the lexical coding path predicate is not a proof of
physical filesystem containment; symlink, mount and process isolation checks belong to the IO
boundary.

## Runtime and recovery evidence

A runtime must interpret the exact admitted operation under the frozen configuration and return a
valid result when it claims success or retains a typed partial value. It must enforce its resource,
permission and containment contracts before returning. The Runner serializes and decodes actual
observations before persisting and consuming them; a rejected representation does not authorize a
logical completion. The pure codec laws establish preservation when the domain premises hold.

`prepare` runs before intent persistence and may inspect state to construct a witness; it must not
perform the protected mutation. `reconcile` may inspect and synchronize existing evidence but must
not repeat the lost operation. These are obligations of the installed IO implementation, not
consequences of its Lean function type.

A durable-intent acknowledgment establishes only the storage adapter's declared durability
contract. A success observation must be backed by the application's real effect/evidence contract.
An uncertain effect must remain uncertain until application-specific evidence settles it; decoding
or rendering a receipt cannot establish that the represented effect occurred.

For Coding, reads rely on validated workspace paths and filesystem identity; edits use preimage and
postimage evidence. Physical process settlement and retained artifacts rely on the sandbox and
artifact adapters. Operator-reported process completion remains explicitly operator-reported.
Neither lexical validity nor a well-shaped result proves those external facts.

For Inventory, the seed is frozen session input and the authoritative state is the mandatory,
validated session-local receipt ledger. Reservation success follows a durable ledger append. An
existing reservation key is reconciled only against the same session ID, operation ID, call ID,
arguments, seed and recomputed stock arithmetic. Recovery must reread and resynchronize the exact
receipt rather than debit again. Missing, torn, conflicting or arithmetically invalid evidence must
refuse settlement. No claim is made about an external warehouse service.

`readOnly` classifies an operation for conservative lost-intent handling. It is not a commutativity
law: an Inventory query can observe different stock before and after a reservation. A future
application must separately establish any stronger independence or reordering claim.

The real IO/recovery tests exercise the adapter assumptions; the pure laws do not replace those
tests or prove operating-system behavior.
