# Query decoder

Repair parseQuery(text) in query.js (CommonJS). Accept an optional leading '?'. Split nonempty segments on '&', and split each at only its first '='. Missing '=' gives an empty value. Decode percent-encoded UTF-8 and convert '+' to space in BOTH names and values. Preserve duplicate keys as arrays in encounter order; return a plain object with own properties, including '__proto__' and 'constructor'. Empty segments are ignored. Invalid percent escapes or UTF-8 raise URIError. Do not interpret a fragment or full URL: input is only a query string.

Only edit: `query.js`. Keep README, public tests, and definitions/specification files unchanged. No third-party dependencies or network access are needed.

Run the visible checks:

```sh
node test_public.js
```
