# Statement handoff

Authoritative source: `/spec/source.txt`, selected theorem
`theorem:cholesky_factorization`; explanatory proof: `/spec/paper.tex`.
The supplied `/spec/support` has no files. Its directory contents were copied
unchanged into Research. No `feedback.json` is present.

## Statement revision record

There was no pre-existing formal statement to revise (Submission.lean only
imported Mathlib). The selected conclusion, constant, dimension quantifier,
symmetry and positive definiteness assumptions are preserved. No requested
backward-error estimate or paper lemma is an assumption. This role leaves
exactly the final theorem proof as `sorry`.

The following modeling details are explicit, rather than silently inherited
from the fallible plan:

* `FloatingPoint` specifies one real rounding map and its relative error on
  in-range exact results. All primitives, including square root, use this map.
  `NoOverflowUnderflow` checks each exact intermediate result of the run.
  In particular, the sqrt guarantee follows directly by applying
  `relative_round` to `Real.sqrt radicand`. This is the intended standard
  rounded-square-root interpretation. The four-operation formula in isolation
  does not imply any statement about an unconstrained square-root primitive;
  the original source has this semantic omission. The formal statement does
  explicitly require standard rounding semantics for sqrt, without assuming
  any diagonal backward bound.
* The dot product is sequential, initialized by its first rounded product.
  The first pivot uses the input entry directly, since subtracting an empty
  dot product from a floating-point input is exact. In particular, it does not
  introduce a fictitious rounding error on `A[0,0] - 0`; this matters for n=1
  and the exact gamma_2 bound. Subsequent subtractions are rounded normally.
* Unit roundoff is explicitly nonnegative. There is no n>0 assumption.
  Successful execution requires nonnegative radicands and a nonzero pivot
  wherever a division uses it; it permits a zero unused final pivot.
* `prefixPairs R i j` comprises exactly the indices k<i in ascending order,
  and Lean pivot i corresponds to source pivot i+1. The stored factor is
  upper triangular. Every recurrence is linked to the same original A and R.
* `perturbation A R` is concretely `R.transpose * R - A`. The target states
  existence of a symmetric perturbation with exact factorization and the
  entrywise bound. Its right side is the matrix product of entrywise absolute
  values, not the absolute value of the Gram product.

## Work for the proof role

Prove scalar sequential-dot expansions and rounding-product bounds from
`relative_round`; do not assume paper lemmas. At the first off-diagonal
pivot count the inverse division factor directly. At the first diagonal
pivot there are two inverse copies of the sqrt factor. At later diagonal
pivots include the subtraction factor and both sqrt factors. Use the actual
R entries for the squares, avoiding the paper's undefined primed factor.
Then use upper triangularity and symmetry to assemble the full componentwise
bound with gamma_(n+1). A natural witness is `perturbation A R`.
