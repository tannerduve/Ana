# Numeric version comparison

Implement `compare(left, right)` for dot-separated nonnegative ASCII integer components. Leading zeros are allowed. Missing trailing components compare as zero, so 1.2 == 1.2.0. Return exactly -1, 0 or 1. Empty components, signs, whitespace, non-ASCII digits and non-strings are invalid and raise ValueError. Support arbitrarily large components.

Only edit: `versions.py`. Keep README, public tests, and definitions/specification files unchanged. No third-party dependencies or network access are needed.

Run the visible checks:

```sh
python3 -m unittest test_public.py
```
