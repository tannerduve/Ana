# Atomic settings transactions

Implement `apply(settings, operations)` in transactions.py. Settings is a dictionary of dictionaries with string keys and JSON values. Each operation is {op:'set'|'delete', path:[nonempty string,...], value:... for set}. Paths traverse dictionaries only; intermediate keys must already exist. Set may create/replace the final key. Delete requires the final key to exist. Operations see earlier operations in the same batch. Reject malformed operations, paths, missing intermediate objects, or missing deletes with ValueError. Return a deep independent updated dictionary; settings and operations must remain unchanged even if a later operation fails. Empty operations returns an independent copy. CLI reads {settings,operations} JSON and prints resulting settings; invalid data exits 2 with no stdout. Work across both API and CLI and use the repository notes to understand the contract.

Only edit: `transactions.py`, `cli.py`. Keep README, public tests, and definitions/specification files unchanged. No third-party dependencies or network access are needed.

Run the visible checks:

```sh
python3 -m unittest test_public.py
```
