# Prove the append law for a recursive total

Complete `total_append` in Proof.lean against the fixed recursive `total` definition. Keep the theorem statement unchanged. The definition is deliberately not Lean's built-in list sum; prove its append law using the available definitions and standard library. No axioms, sorry/admit, unsafe substitutions, or disabled kernel checks.

Only edit: `Proof.lean`. Keep README, public tests, and definitions/specification files unchanged. No third-party dependencies or network access are needed.

Run the visible checks:

```sh
lean -o Definitions.olean Definitions.lean && LEAN_PATH=. lean -o Proof.olean Proof.lean && LEAN_PATH=. lean Spec.lean
```
