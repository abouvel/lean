# Decisions and status

Implemented `Research/Submission.lean`, already connected through the supplied root `Research.lean` import. No configuration or specification files changed.

## Representation
- Represent active levels by lists, with zero-based indices.
- At each round split at `(length + 1) / 2`, pair the two blocks in order, and return an unmatched entry unchanged. Thus the offset pairing and carry branch are explicit rather than adjacent-pair reduction or zero padding.
- Rounding additions may depend deterministically on both level and output index. `roundedAdd` encodes `(a+b)*(1+δ)`; carries do not invoke it.
- Use `Nat.clog 2 n` for ceiling base-two logarithm, characterized by `depth n ≤ t ↔ n ≤ 2^t`.

## Completed proofs
- Each round has ceiling-half active length.
- Any nonempty input bounded by `2^t` reaches a singleton after `t` rounds; consequently the algorithm reaches a singleton at its stated logarithmic depth.
- Each exact-arithmetic round preserves the sum, and the full exact algorithm preserves the original list sum.
- For an arbitrary list of bounded roundoff factors, the product deviation is bounded by `(1+u)^length - 1`, and by `gamma length u` when `length*u < 1` and `0 ≤ u`.
- These declarations compile without `sorry` or new axioms.

## Failed approaches / corrections
- Real division made `gamma` require a `noncomputable` declaration; corrected after the initial compiler check.
- The complete occurrence-indexed invariant was not reached within the builder time limit. The path-product lemma alone does not imply the theorem about this algorithm.

## Remaining obligations
This is a partial formalization, not verification of the complete assignment or Theorem 3.1.
- Establish an occurrence-indexed expansion for the computed singleton, preserving each occurrence even for repeated equal inputs.
- Prove every such occurrence path contains at most `depth n` rounded additions, treating carries as identity factors.
- Connect that invariant to `path_gamma`, including padding paths with zero factors or monotonicity of gamma.
- Construct the componentwise perturbations and prove the final backward-error identity and all componentwise bounds for arbitrary nonempty real lists.
- State/prove explicitly the equivalence between repeated ceiling-halving offsets and the source's global `ceil(n / 2^(level+1))` notation.

Compilation of the partial library does not discharge these remaining obligations.
