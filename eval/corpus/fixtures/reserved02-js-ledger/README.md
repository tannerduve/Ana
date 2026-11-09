# Normalize and report a small event ledger

Implement the public API `summarize(events)` in index.js by repairing normalize.js and report.js. Each event has account (nonempty string), delta (safe integer), and id (nonempty string). Duplicate IDs with identical account/delta are ignored; conflicting duplicate IDs throw RangeError. Invalid events throw RangeError. Return records sorted by account with {account,balance,events}; events counts unique IDs, and omit accounts whose balance is zero. Intermediate and final balances must stay safe integers, otherwise throw RangeError. Do not mutate input or share output objects with input. Preserve the facade and tests. The architecture notes define the two-stage flow; ensure both stages work through the public API.

Only edit: `normalize.js`, `report.js`. Keep README, public tests, and definitions/specification files unchanged. No third-party dependencies or network access are needed.

Run the visible checks:

```sh
node test_public.js
```
