# Percent decoding with UTF-8 validation

Repair `pub fn decode(text: &str) -> Result<String, String>` in solution.rs. Replace '+' with space, decode each %HH byte using ASCII hex digits of either case, and then validate the entire output as UTF-8. Unescaped Unicode is preserved. Incomplete/invalid escapes or invalid UTF-8 return Err; error wording is unconstrained. Do not panic on any input. Standard library only.

Only edit: `solution.rs`. Keep README, public tests, and definitions/specification files unchanged. No third-party dependencies or network access are needed.

Run the visible checks:

```sh
rustc --edition=2024 test_public.rs -o /tmp/task-public && /tmp/task-public
```
