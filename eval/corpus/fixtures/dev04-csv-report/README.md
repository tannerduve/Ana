# CSV category report

Implement `report(text)` and its stdin CLI. Parse CSV with a header containing exactly `category,amount` in either order. Honor CSV quoting and embedded newlines. Amounts are signed ASCII integers (optional single + or -), with no surrounding whitespace. Categories are nonempty strings. Ignore completely blank physical rows; reject malformed row widths, duplicate/unknown headers, bad amounts and empty categories with ValueError. Return sorted records {category,total,count}. CLI accepts `--min-total N` and keeps totals >= N; default keeps all. Invalid CSV or option exits 2 and prints no stdout.

Only edit: `report.py`, `cli.py`. Keep README, public tests, and definitions/specification files unchanged. No third-party dependencies or network access are needed.

Run the visible checks:

```sh
python3 -m unittest test_public.py
```
