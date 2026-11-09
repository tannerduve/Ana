# Merge half-open intervals

Export `mergeIntervals(intervals)` from intervals.js (CommonJS). Every interval is [start,end] with safe-integer coordinates and start<=end. Drop empty intervals. Sort and merge overlaps AND touching boundaries. Return new arrays, without changing input or sharing interval arrays. Reject malformed intervals with RangeError. Empty input returns [].

Only edit: `intervals.js`. Keep README, public tests, and definitions/specification files unchanged. No third-party dependencies or network access are needed.

Run the visible checks:

```sh
node test_public.js
```
