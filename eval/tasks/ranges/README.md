# Repair `parse_ranges`

Fix `ranges.py` so `parse_ranges(text: str) -> list[int]` implements this contract:

- Input is a comma-separated sequence of positive integer items and inclusive ascending ranges, such as `4,1-3,2`.
- Return all selected integers, sorted ascending with duplicates removed.
- Ignore leading/trailing whitespace around the whole input, each item, and each range endpoint. Thus ` 1 , 2 - 4 ` is valid.
- An integer consists only of ASCII decimal digits (`0` through `9`) and its value must exceed zero. Leading zeros are allowed. Signs, underscores, decimal points, and non-ASCII digits are invalid.
- A range contains exactly two integers separated by one hyphen. Equal endpoints are allowed; a lower endpoint greater than its upper endpoint is invalid.
- An empty or whitespace-only whole input returns `[]`.
- Empty items (including trailing commas), malformed items, reversed ranges, and nonpositive integers raise `ValueError`.

Inputs to this task are strings, and numerical examples are small. No behavior for other input types or special handling for huge ranges is required.

Modify `ranges.py`. Keep this specification and the existing tests unchanged. You may inspect files and run the tests with:

```sh
python3 -m unittest -v
```

Explain the change and the checks you ran. A final answer alone does not establish success: an external evaluator checks the resulting implementation.
