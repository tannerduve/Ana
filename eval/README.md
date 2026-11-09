# Development smoke evaluation

`runner/live_smoke.py` runs one self-authored Python repair task through the real harness and Anthropic API. It is development evidence, not a held-out benchmark, reliability estimate, or Pi comparison.

Build the harness, install Linux `bubblewrap`, and provide `ANTHROPIC_API_KEY` in the environment or a private credential file:

```sh
lake build
python3 eval/runner/live_smoke.py --model MODEL_ID
# Alternatively add: --key-file /private/credential-file
```

Each run creates a fresh fixture workspace and private evidence directory. The model must repair `parse_ranges` while preserving its specification and public tests. A separate checker evaluates 43 cases and verifies those two files remain unchanged. The baseline must fail before the model runs. Success requires a normal harness finish, passing independent checks, unchanged fixtures, readable session state, and no watchdog timeout. Review the resulting patch for checker bypasses before reporting task success.

The live model runs in a bubblewrap namespace containing its workspace, the harness executable, configuration, session storage, and system runtime (including curl and libcrypto). Host home directories and the independent checker are absent. Afterward, the checker runs in a separate namespace without the API credential. Commands are explicitly allowed for this disposable task; network access is shared so the provider is reachable.

This arrangement is not protection against a malicious candidate. The process tree shares `/proc`, so filtering a command's inherited environment does not guarantee that the API key is inaccessible through another process's environment. Session storage is also writable from that namespace. The task is a benign development fixture; no stronger credential-isolation claim is made.

The evidence directory contains configuration, structured events, diagnostics, the final workspace, session journal, checker results, and a summary with timing, dispatch counts, reported usage, and the executable hash. Raw events and journals contain task content and model responses: keep them private and publish reviewed aggregate results and patches. Usage counters do not constitute exact billing. One successful run demonstrates this task only; retries, failures, and infrastructure errors must remain in later aggregate reporting.
