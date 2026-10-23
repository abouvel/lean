# Decisions and status

The implementation is in `/workspace/Research/Submission.lean`, already imported by the root `Research.lean`. Project configuration and `/spec` were not changed.

## Completed
- Implemented a deterministic offset-pairing round by splitting at `ceil(current length / 2)`, pairing corresponding entries of the two halves, and returning unmatched entries unchanged. There is no rounded addition with zero on the carry branch.
- Implemented iteration for `Nat.clog 2 n` rounds and extraction of the result.
- Proved round length, preservation of nonemptiness, reduction to exactly one value at the prescribed logarithmic depth, and the least-capacity characterization of that depth.
- Proved conservation of exact sums and exact-arithmetic correctness for all nonempty real lists.
- Proved a general additive-mass invariant and instantiated it with multiset occurrence labels. This tracks multiplicity even when input values coincide.
- Defined the relative rounding model, gamma, and the full requested componentwise stability proposition; proved the local absolute-error estimate.

## Important choices
- `Nat.clog 2 n` represents the integer ceiling logarithm without using real logarithms.
- The operation is an explicit argument, so exact and rounded evaluation share an implementation. The supplied no-overflow/no-underflow assumption is represented by validity of the relative-error model at every addition.
- Labels are arbitrary natural-number multisets carried alongside computed values.

## Failed approaches / limits
- The first compiler run rejected computable real division in gamma; marking that definition noncomputable resolved it.
- The hard builder limit prevents completing the global numerical analysis. No axioms or `sorry` placeholders were introduced to hide it.

## Remaining obligations
The assignment is NOT complete. There is no theorem proving `BackwardStable` from the rounding model, nonnegative unit roundoff, nonempty input and `depth * u < 1`. In particular, the per-occurrence path/product representation and the gamma bound on those products remain to be formalized. Also absent are an explicit equivalence between the recursive current-length offsets and the paper's `ceil(n / 2^(level+1))` offsets, and a theorem connecting the tagged evaluator's value projection to the untagged evaluator. These gaps must be resolved before claiming Theorem 3.1 has been verified.

## Validation
`lake build` compiled `Research.Submission` and the root import successfully (one unused-simp-argument warning). This verifies only the completed declarations listed above, not the unproved componentwise stability assertion.
