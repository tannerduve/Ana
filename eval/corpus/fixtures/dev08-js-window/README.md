# Moving-window sums

Export windowSums(values, width) from window.js. Width must be a positive integer and values an array of finite numbers. Return sums for each complete contiguous window of exactly width elements. Width greater than length returns []. Preserve input. Invalid width or elements throw RangeError. Use a rolling sum so a long array with a wide window does not require quadratic work.

Only edit: `window.js`. Keep README, public tests, and definitions/specification files unchanged. No third-party dependencies or network access are needed.

Run the visible checks:

```sh
node test_public.js
```
