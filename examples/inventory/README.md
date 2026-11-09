# Inventory

This application queries and reserves local stock through typed tools. It uses the same durable runner, budgets, permissions, compaction and recovery machinery as the coding application. It cannot execute commands or choose arbitrary paths. Each session owns its inventory; reservations do not change the input file or another session's stock.

From the repository root after building `harness`, run:

```sh
.lake/build/bin/harness run --application inventory \
  --config examples/inventory/config.json \
  --data examples/inventory/stock.json \
  --task "Find the warehouse with the greatest replenishment shortfall; list all affected SKUs using pages of one, and look up one item." \
  --script examples/inventory/script.json \
  --session /tmp/inventory-example-session --json
.lake/build/bin/harness inspect /tmp/inventory-example-session
.lake/build/bin/harness replay /tmp/inventory-example-session
```

Use a fresh session path. The scripted model makes four requests and four tool calls: warehouse totals, two pages, and one item lookup. The tools compute their answers from `stock.json`: south needs 32 units (30 gloves and two labels). Scripted responses exercise execution and persistence without network access or credentials; their final prose is a fixture, not evidence of model reasoning.

The updated dataset changes only the gloves' on-hand quantity from zero to 29. Run with `stock-updated.json`, `script-updated.json` and a different session path: north now has the largest shortfall, at 15 units. These are editable example data, not embedded query answers.

Add `--yield-after 3` to a fresh run to suspend after three durable completions (exit 75), then use `harness resume SESSION --json`. The starting dataset and script are frozen in the session; resume does not reread their source files. `toolPolicy` in the config accepts `allow`, `ask` or `deny`. An approval covers one exact operation. A lost read completion becomes an explicit unknown-result error; recovery does not silently repeat it.

To exercise a stock change, use `script-reserve.json` and a fresh session path with the task `Reserve four N-CABLE units, then check the remaining stock.` It reserves four of the twelve units and looks up the remaining eight. The receipt records the harness-assigned operation ID. If the debit commits but its reply is lost, resume reconciles that receipt without another debit. Missing or conflicting evidence stops recovery; see the [recovery contract](../../docs/Applications.md#recovering-a-committed-reservation).

`lake exe inventory_recovery_contracts` runs the process-interruption tests without credentials.

`lookup` returns an optional item, `low_stock` a page with `matched`, `offset`, `nextOffset` and `truncated`, and `warehouse_totals` an array of summaries. Follow `nextOffset` with the same warehouse until it is null. Result decoding rejects another operation's shape, a different SKU or warehouse, or a mismatched page. Data is limited to 1 MiB, 512 unique SKUs and 64 warehouses; page size is 1–100.
