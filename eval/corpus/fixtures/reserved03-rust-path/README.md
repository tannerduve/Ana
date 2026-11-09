# Lexical relative-path normalization

Implement `pub fn normalize(text: &str) -> Result<String,String>`. Paths are slash-separated and relative. Reject leading '/', any backslash, any NUL, or a '..' component that would escape above the root. Ignore empty and '.' components; '..' removes the previous ordinary component. Preserve Unicode and other characters literally. Return '.' for an empty normalized path. This is lexical normalization, not filesystem or symlink containment. Error wording is unconstrained.

Only edit: `solution.rs`. Keep README, public tests, and definitions/specification files unchanged. No third-party dependencies or network access are needed.

Run the visible checks:

```sh
rustc --edition=2024 test_public.rs -o /tmp/task-public && /tmp/task-public
```
