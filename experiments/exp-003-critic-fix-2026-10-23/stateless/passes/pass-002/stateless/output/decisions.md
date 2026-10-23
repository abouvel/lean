# Decisions and results

- Preserved Algorithm 1's original offset `ceil(n / 2^(level+1))`, with no addition or error factor in an unchanged carry branch. The input list is indexed before tree construction, preserving duplicate occurrences.
- Added `step_length` and `rounds_length`, proving the exact ceiling length invariant. `forest_singleton` proves every nonempty input returns exactly one tree, preserves all indexed occurrences, and has height at most `Nat.clog 2 n` (the ceiling logarithm).
- Proved `gamma_step` from absolute relative-error bounds by a triangle inequality and positive-denominator algebra. `terms_bound` derives the path-factor estimate by tree induction; no factor estimate is assumed.
- `theorem_3_1` applies to every nonempty real list, arbitrary nonnegative unit roundoff and valid per-addition relative errors, under depth*u < 1. It constructs a list of perturbations tagged with original indices and values, proves its occurrence permutation, the returned-result sum representation, and every componentwise gamma bound. This indexed-list representation avoids assuming distinct input values.
- `algorithm_exact` additionally proves the exact-arithmetic result equals the original list sum.
- Initial repair attempts failed on a natural-number scalar multiplication normalization, a list singleton lemma name, and reduction of a match before rewriting. These were corrected. The numerical estimate uses positive-denominator clearing rather than an assumed product bound.
- Direct Lean checking of Research/Submission.lean succeeds, without placeholders or custom axioms. The root imports Research.Submission. Full root build is checked separately below.
- Remaining limitation: dedicated executable regression examples of the requested intermediate numerical levels were not added; the general algorithm and proof include odd, singleton, and duplicate cases.
