# Verified Lean patterns for binary reduction

```text
artifact_id: validated-lean-binary-reduction-001
status: verified
supporting_runs: run-2026-10-11-algorithm1
```

[Supporting run](../2026-10-11-algorithm1-offset-reduction.md).
These full lessons are not the experiment's restricted `memory/` snapshot.

## Offset-paired reduction

Represent one parallel level as a forest of trees. Split at
`(forest.length + 1) / 2`, combine corresponding entries from the two halves,
and carry an unmatched entry unchanged.

## Preservation invariant

Use a leaf `Multiset` when a tree algorithm reorders inputs. List equality is
too strong; set equality loses duplicate multiplicity. Prove preservation for
one round and lift it by induction over repeated rounds.

## No false rounding on carry

An unmatched partial sum must remain the same tree. Do not wrap it in a node
with zero, because rounded addition with zero can still introduce a relative
error in the abstract model.

## Logarithmic depth

Separate the proof into:

1. one round changes length from `n` to `(n + 1) / 2`;
2. repeated ceiling-halving reaches `1` after `Nat.clog 2 n` rounds;
3. one round increases the maximum tree depth by at most one.

Combining these gives final depth at most `Nat.clog 2 n`.

## Lean proof-engineering observations

- Rebuild changed imported modules before diagnosing missing declarations from
  a dependent module; stale `.olean` files can hide new definitions.
- Rewrite rational inequalities over explicitly positive denominators before
  asking nonlinear arithmetic to finish them.
- In this pinned Mathlib version, the real absolute-value triangle inequality
  is `abs_add_le`.
- When concrete `Nat.clog` reduction is unstable, prove the small equality with
  `native_decide` and rewrite with it.

## Scope

These patterns are verified for the repository's abstract real-valued
floating-point model and Algorithm 1 implementation. They do not establish
IEEE 754 bit-level behavior or probabilistic error bounds.
