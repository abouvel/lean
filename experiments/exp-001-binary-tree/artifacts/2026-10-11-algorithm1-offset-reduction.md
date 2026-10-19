# Algorithm 1 offset reduction

```text
artifact_id: run-2026-10-11-algorithm1
date: 2026-10-11
project: binary-tree-reduction
status: verified
memory_mode: stateless
retrieved_artifacts: none
verification: bash pipeline/verify.sh
```

## Request

> Implement Algorithm 1 exactly. First make the five-input test produce levels
> `[2,3,4,5,6]`, `[7,9,4]`, `[11,9]`, `[20]`. Verify that unmatched elements
> are carried without rounding. Then prove that for every nonempty list, the
> final tree preserves all inputs and has depth at most `Nat.clog 2 n`.

## Target

Implement the paper's offset-paired reduction as a list-to-tree algorithm and
connect its structural guarantees to the existing floating-point tree theorem.

## Result

- The exact five-input levels are proved in Lean.
- The unmatched value `4` remains a leaf instead of becoming an addition node.
- Every nonempty list produces one final tree.
- The final tree preserves the input multiset, including duplicate values.
- Its depth is at most `Nat.clog 2 inputs.length`.
- Its exact sum equals the input list sum.
- The construction composes with the general `gamma` backward-error theorem.

## Decisions and reasoning

- A forest represents the active partial sums at one algorithm level.
- Each round splits at `(n + 1) / 2`, pairs corresponding entries from both
  halves, and carries any unmatched entry from the first half.
- Preservation uses `Multiset`, not list equality, because offset pairing
  changes leaf order while preserving every occurrence.
- The depth proof tracks a uniform bound over the entire active forest.
- The termination-length argument follows repeated ceiling-halving and the
  recurrence for `Nat.clog 2 n`.

## What worked

- Separating numeric length recurrence from tree structure simplified the
  logarithmic-depth proof.
- Proving one-round invariants first made the repeated-round proofs inductive.
- A concrete five-input shape test detected the difference between adjacent
  pairing and the paper's offset pairing.

## What failed

- List equality was initially considered as the preservation invariant. It is
  incorrect because Algorithm 1 reorders leaves.
- Direct simplification did not normalize all multiset additions; the proof
  required explicit commutative-monoid rearrangement.
- Direct reduction of `Nat.clog` in the numeric example was unreliable; a
  separately verified equality `Nat.clog 2 5 = 3` made the test stable.

## Reusable observations

- For tree algorithms that reorder data, prove multiset preservation before
  proving value-level properties.
- Treat carried nodes structurally as unchanged trees; do not model them as an
  addition with zero, because that would introduce a false rounding step.
- For divide-by-two algorithms, isolate a theorem about the induced length
  recurrence before proving the structural depth theorem.

## Evidence

- [Implementation](../../../lean/Research/Projects/BinaryTreeReduction/Algorithm.lean)
- [Five-input checks](../../../lean/Research/Projects/BinaryTreeReduction/Examples.lean)
- [Floating-point bridge](../../../lean/Research/Projects/BinaryTreeReduction/Reduction.lean)
- [Detailed baseline record](../notes/baseline-002.md)
- Verification result: 8,036 build jobs completed; placeholder and custom-axiom
  scans passed.

## Remaining limitations

- This run proves the deterministic relative-error result.
- It does not prove the separate probabilistic dot-product theorem.
- The floating-point model is abstract and is not a bit-level IEEE 754 model.

## Metrics

```text
wall_time: unknown
tokens: unknown
cost: unknown
aristotle_calls: 0
```
