"""Parse comma-separated selections of positive integer identifiers."""


def parse_ranges(text: str) -> list[int]:
    """Return the identifiers represented by text; see README.md for the contract."""
    if not text.strip():
        return []
    values = []
    for item in text.split(","):
        if "-" in item:
            start, stop = item.split("-")
            values.extend(range(int(start), int(stop)))
        else:
            values.append(int(item))
    return values
