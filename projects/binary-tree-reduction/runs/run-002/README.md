# Run 002 - exact Algorithm 1 construction

## Objective

Implement the paper's offset-paired reduction, verify the five-input example,
and prove input preservation plus the `Nat.clog 2 n` depth bound for every
nonempty input list.

## Requested acceptance test

For inputs `[2, 3, 4, 5, 6]`, the exact partial-sum levels must be:

```text
[2, 3, 4, 5, 6]
[7, 9, 4]
[11, 9]
[20]
```

The unmatched `4` must be carried as the same leaf without an addition node.

## Approach

- Split each active forest at `(n + 1) / 2 = ⌈n/2⌉`.
- Pair corresponding entries from the two halves.
- Carry an unmatched entry from the longer first half unchanged.
- Run exactly `Nat.clog 2 n` rounds.
- Track leaves with a `Multiset` so duplicate input values are preserved.
- Track a uniform depth bound for every active tree after each round.

## What worked

- The five-input level equality and exact final tree are proved by reduction.
- One round preserves the complete leaf multiset.
- Repeated ceiling-halving reaches one active tree after `Nat.clog 2 n` rounds.
- Every round increases maximum depth by at most one.
- The resulting tree has the same exact sum as the input list.
- The algorithm theorem composes directly with the general floating-point
  backward-error theorem.

## Repairs made during development

- Input order is not preserved by offset pairing, so list equality is the
  wrong invariant. A multiset records every input with multiplicity while
  allowing the algorithm's reordering.
- The earlier four-input explanatory tree used adjacent pairing. Algorithm 1
  uses offset pairing; the new tests inspect the exact Algorithm 1 shape.
- The logarithmic proof follows the recurrence
  `clog 2 n = clog 2 ((n + 1) / 2) + 1` for `n ≥ 2`.

## Aristotle

Aristotle was not used. This remains part of the manual baseline.

## Verification

- Run `bash pipeline/verify.sh`.
- The full project must build without `sorry`, `admit`, or custom axioms.
