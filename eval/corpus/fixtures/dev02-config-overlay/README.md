# Recursive configuration overlay

Implement `overlay(base, patch)`. Both top-level values must be dictionaries. Merge recursively only when both old and new values are dictionaries; otherwise replace the old value. Lists replace whole lists. A null value is a value, not a deletion marker. Return a deep independent copy: neither argument nor any nested object may be mutated or shared with the output. Keys are strings. Reject a non-dictionary top-level argument with ValueError.

Only edit: `overlay.py`. Keep README, public tests, and definitions/specification files unchanged. No third-party dependencies or network access are needed.

Run the visible checks:

```sh
python3 -m unittest test_public.py
```
