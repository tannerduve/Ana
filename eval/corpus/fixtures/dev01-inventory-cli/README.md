# Inventory aggregation and CLI

Repair `summarize(rows)` in `inventory.py` and make `cli.py` consume one JSON array from stdin. Each row has `sku` (nonempty string), `quantity` (integer, excluding booleans; may be negative), and `unit_cents` (nonnegative integer, excluding booleans). Reject malformed rows with ValueError. Return one object per SKU, sorted by SKU, with `sku`, total `quantity`, and total `value_cents` (sum quantity*unit_cents). Different prices for one SKU are allowed. Do not mutate input. CLI prints the result as JSON; invalid input exits 2, prints no stdout, and writes a diagnostic to stderr.

Only edit: `inventory.py`, `cli.py`. Keep README, public tests, and definitions/specification files unchanged. No third-party dependencies or network access are needed.

Run the visible checks:

```sh
python3 -m unittest test_public.py
```
