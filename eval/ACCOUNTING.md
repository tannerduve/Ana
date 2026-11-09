# Evaluation spending

Live runs require a shared campaign ledger and a named allocation. Every broker
durably reserves an amount before contacting Anthropic. Complete usage settles
that reservation; missing usage remains charged. Corrupt or interrupted accounting
stops admission. An observed charge above its reservation freezes the campaign.

Within a broker, the next request waits for the previous request's accounting to
finish, even if the client has already received the response. Unknown charges or
failed broker-record writes stop subsequent work. A storage failure does not
turn an already settled charge into unknown usage. Optional response-body capture
is separate: failure to save those diagnostic bytes does not change accounting.

Each run defaults to a 4,096-token output ceiling. An explicit frozen setting may
select an integer from 1 through 8,192: public runs use `--max-output-tokens`, and
sustained modes use `config.maxOutputTokens`. The resolved ceiling is recorded in
the plan/result and each admitted request. Requests above it are rejected before
any campaign reservation. Reservations still use the actual requested output
allowance and unchanged conservative input-byte formula; missing usage retains
the full reservation. A larger output ceiling does not raise the byte, attempt,
allocation or campaign spending limits.

New plans require versioned request evidence saved with the reservation before
forwarding: the exact outbound body SHA-256, a normalized system/messages digest
(object order and equivalent decimal spellings normalize), and indexed user-text
hashes on the first request, without retaining raw requests, headers or credentials.
Lean audits compare the normalized contexts with journal reconstruction, while
both engines must match the frozen full task text in their first request; these
hashes do not prove delivery or provider instruction compliance, and a dispatch
intent alone does not satisfy the first-task check.
Construction or storage failure stops admission; legacy rows explicitly have
unavailable request evidence and retain their original qualification criteria.

The campaign has a $150 authorization. Its original runs accounted for
$19.211732 before this ledger was created. The command below reproduces the
initial allocation; it is not a statement of the remaining balance. For an
existing campaign, use `inspect` instead of initializing another ledger.

From `eval/`, with an existing private parent:

```sh
python3 runner/campaign.py init /private/eval/pilot-budget \
  --prior-report reports/2026-11-09-campaign.json \
  --allocation development=12 --allocation heldout=78 \
  --allocation long=28 --allocation reserve=12.788268
python3 runner/campaign.py inspect /private/eval/pilot-budget
```

Pass `--campaign-dir /private/eval/pilot-budget --allocation development` to
development runs. Each runner's `--budget` is an additional ceiling. All processes
in this campaign must use the same ledger; creating another ledger does not grant
another spending authorization.

Accounting uses standard, global Opus 5.5 pricing: $4 input, $20 output, $5 for
five-minute cache writes and $0.20 for cache reads per million tokens. Fast mode,
regional pricing and extended-cache requests are rejected. Reservations use the
higher $8 cache-write rate conservatively. Rates were checked on November 9,
2026 against [Anthropic's pricing](https://platform.claude.com/docs/en/about-claude/pricing).

This controls local admission under the stated pricing assumptions. It is not a
provider billing cap or an invoice. Keep the ledger outside agent mounts and Git.
