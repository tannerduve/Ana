# Bounded tail retention

Repair `pub fn tail(values: &[i64], capacity: usize) -> Vec<i64>`. Return the last min(length, capacity) elements in their original order. Zero capacity returns an empty vector; very large capacities are valid. Input remains unchanged. Avoid arithmetic underflow and avoid allocating capacity-sized storage when capacity is larger than input.

Only edit: `solution.rs`. Keep README, public tests, and definitions/specification files unchanged. No third-party dependencies or network access are needed.

Run the visible checks:

```sh
rustc --edition=2024 test_public.rs -o /tmp/task-public && /tmp/task-public
```
