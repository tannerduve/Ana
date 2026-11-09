# Repair a list proof after an API rename

Fix the proof of `reverse_twice` in Proof.lean. Its exported theorem must still prove, for every list of natural numbers, that reversing twice returns the original list. The old lemma name is no longer available. Do not change the theorem statement, add axioms, use sorry/admit, skip kernel checks, replace implementations, or change Definitions/Spec. Only Lean's pinned standard library is available.

Only edit: `Proof.lean`. Keep README, public tests, and definitions/specification files unchanged. No third-party dependencies or network access are needed.

Run the visible checks:

```sh
lean -o Definitions.olean Definitions.lean && LEAN_PATH=. lean -o Proof.olean Proof.lean && LEAN_PATH=. lean Spec.lean
```
