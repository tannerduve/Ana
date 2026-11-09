# Evaluation development

The product and evaluations share one repository. Build the product at the root,
then run `lake build` in `eval/`; its explicit path dependency is `..`. Rebuild
both after changing product code. The proxy identity binds actual loaded product
sources and the proxy executable, while runner admission separately rejects a
stale product executable without silently rebuilding it.

To reuse already-built product dependency caches locally, an optional ignored
symlink avoids duplicate downloads:

```sh
# From eval/, only when .lake/packages does not already exist:
mkdir -p .lake
ln -s ../../.lake/packages .lake/packages
lake build
```

An alternative product checkout requires both a Lake package override and the
same explicit runner selection. Lake's `--packages FILE` accepts a manifest with
a path entry named `lean_harness`; set its `dir` to the absolute product path,
`configFile` to `lakefile.lean`, `manifestFile` to `lake-manifest.json`, and
`inherited` to false. Keep overrides under `.lake/`, then run:

```sh
lake --packages .lake/local-packages.json build eval_tools_identity
export LEAN_HARNESS_ROOT=/absolute/path/to/the/same/product
python3 Tests/evaluation_baseline.py
```

These are provenance checks under a trusted build environment, not binary
attestation. Git history rewrites do not change content identity. Historical
sessions still require the exact executable used to create them; a rebuilt
binary must not be substituted for a recorded one.
