# Applications and typed tools

The harness supplies one execution engine. An application supplies the operations that engine can admit and interpret. Coding and inventory are the two installed applications; selection is explicit at session creation.

## The interface

A tool interface consists of a call type and a family of possible observations:

$$
T(X)=\sum_{c:\mathsf{Call}}(\mathsf{Observation}(c)\to X).
$$

This is a polynomial functor: calls are its shapes and possible observations are its positions. `ToolAPI.functor` constructs it using Mathlib's `PFunctor`. `InteractionF` adds the other harness actions. The executable coalgebra is `step : State app → HarnessF app (State app)`.

The full `Application` record supplies more than this mathematical signature:

| Field group | Purpose |
| --- | --- |
| `Operation`, `Result` | Typed domain operations and their dependent results |
| Operation/result codecs | Encode durable records and decode results for the exact saved call |
| `decode`, `schemas`, `name`, `args` | Validate model proposals, advertise tools and display exact approvals |
| `policy` | Classify an operation as allowed, denied or requiring approval |
| `requiredCapabilities` | Declare every resource required by an operation; hard ceilings apply before approval |
| `render` | Present a typed result to the model through the common result envelope |
| Recovery contracts | Classify lost reads, validate evidence and resolve uncertain effects conservatively |

The engine adds call IDs, validates whole batches, stores queues, issues grants and reserves budgets. The session-wide `toolPolicy` can restrict an application policy: denial takes priority, then approval, then allowance. Application callbacks cannot replace session state or alter counters. The application is selected by trusted startup code, never by model output or repository instructions.

The frozen [capability policy](Capabilities.md) can further restrict paths, process
invocations, artifacts and namespaced application resources. Every declared access
must be permitted by every policy layer; approvals cannot override this check.

`ApplicationIO.Runtime app` initializes application resources once, then implements one admitted operation at a time. The runner supplies the session identity and logical operation ID to preparation, execution and reconciliation. These identify the same operation across restart; the model cannot choose them. The shared runner owns provider calls, approval, cancellation, session locking, persistence ordering and continuation.

## Two instances

Coding uses the existing file/process tools. Its result family currently uses the common `ToolResult` type for every operation. Its recovery rules include edit preimage/postimage checks, explicit process resolution and the sandbox's settled-timeout contract.

Inventory has distinct result types:

| Operation | Result |
| --- | --- |
| `lookup sku` | `Option Item` |
| `low_stock warehouse offset limit` | A bounded page of replenishment rows |
| `warehouse_totals` | `Array WarehouseSummary` |
| `reserve sku units` | A receipt with operation identity, quantity and remaining stock |

The caller supplies local JSON data. Startup freezes it as the session's starting stock. Reservations debit that stock in a separate local ledger; queries use the starting data plus committed reservations. Each session owns its inventory. This example does not connect to a warehouse service or share stock between sessions. Tools cannot choose file paths or launch processes. `toolPolicy` can allow, deny or require exact approval for any operation.

The provider receives only the selected application's schemas, carried in the recorded model request. Summary requests advertise no tools. A coding tool proposed during an inventory session fails whole-batch admission.

## Persistence and guarantees

Schema 7 records the installed application ID/version, configuration and executable identity. Resume selects that exact application and refuses incompatible sessions. Inventory version 2 adds reservations; existing sessions require their original binary and application version.

Reply decoding is indexed by the actual emitted call. Inventory decoding rejects another operation's result shape and checks identifiers and page bounds. Before recording a completion, the runner validates its serialized representation and consumes the decoded observation, so live execution and replay use the same codec.

Lost read results become explicit unknown-result failures. They are not automatically executed again. Applications must provide evidence or operator resolution rules for uncertain mutations; a generic interface does not provide exactly-once execution. Resolution hooks return settled success/failure, not arbitrary next states.

The common proofs concern admission, bookkeeping and transition structure. An application's policy remains a specification that needs review, and its IO implementation needs contract tests. The coding filesystem and sandbox claims do not automatically apply to a new application.

## Recovering a committed reservation

The inventory ledger and harness journal serve different purposes. One inventory record commits both the stock debit and its receipt. The harness journal records whether the engine received that receipt.

| Interruption point | Resume behavior |
| --- | --- |
| Harness completion is durable | Replay the saved result without another debit |
| Reservation is durable, but its reply was lost | Read and validate the matching receipt, then record a resolution without another debit |
| Intent exists, but no receipt can be established | Leave the operation unresolved; do not reserve again |
| Ledger is torn, corrupt or inconsistent with the saved operation | Refuse automatic recovery and retain the evidence |

Receipt validation binds the session, operation ID, call ID, SKU and quantity. Ledger replay also checks the frozen starting data and every stock change. Insufficient stock produces an ordinary failure without a debit. Reusing a committed operation ID with matching arguments returns its receipt; changing the arguments is rejected.

The [reservation proof](../Harness/Proofs/InventoryReservations.lean) establishes exact subtraction, sufficient stock and preservation of other items for the pure update. It does not establish that a debit reached storage. The [recovery tests](../Tests/InventoryRecovery.lean) run separate processes, stop after the durable debit and check that resume records one result without changing stock again.

Creation writes a ledger header bound to the session and starting data. Resume requires it; a missing ledger cannot reset stock. The ledger uses checksummed frames and durable flushes. Its lock serializes access, and recovery flushes observed evidence before accepting it. These are adapter obligations tested with real files and interrupted execution. The pure core checks the supplied evidence and advances through its usual continuation. This does not make arbitrary external services exactly-once, nor protect local records against a malicious writer.

## Adding an application

1. Define operation/result types and strict codecs in Lean.
2. Supply schemas, decoding, policy, required capabilities, result rendering and conservative recovery contracts.
   State independent validity predicates and prove the [application laws](ApplicationContracts.md)
   for operation/result codecs and model-visible rendering. State and prove a complete
   capability classification, including preparation reads and aggregate disclosures.
3. Implement `ApplicationIO.Runtime app`, keeping external resource access inside its tools.
4. Register the application in the CLI and freeze its validated input at startup.
5. Test actual calls, denied proposals, serialization, interruption and resume through the shared engine.

Applications are compiled in. Dynamic plugins, a multi-agent coordinator and Aleph Matrix integration are separate work. A coordinator can invoke this harness for individual agent sessions and consume JSONL events.
