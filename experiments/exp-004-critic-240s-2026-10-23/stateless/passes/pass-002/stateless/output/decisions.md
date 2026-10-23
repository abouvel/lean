# Repair pass

The original /spec/source.txt remains authoritative. No specification or project configuration was changed. Research.lean imports Research.Submission.

## Completed

Kept Algorithm 1's simultaneous offset pairing and unchanged unavailable-partner branch. Kept the explicit relative-error model with absolute error bounds and nonnegative unit roundoff. Real scalar inputs are the interface.

Added rounds_width: after k rounds, width <= m iff original width <= 2^k*m. Derived the exact natural ceiling-division width and algorithm_offset, identifying the implementation offset with ceil(n/2^(k+1)).

Added rounds_nonempty and algorithm_singleton: every nonempty real list produces exactly one tree after Nat.clog 2 n rounds, the algorithm returns it, and its depth is at most that ceiling logarithm. Existing logarithmic_depth identifies this with the real ceiling logarithm.

Added algorithm_coefficients and algorithm_leaf_backward_error: the actual returned tree has the ceiling-log gamma bound, and its evaluation equals the sum of individually perturbed tree leaves. These use the original roundoff and depth hypotheses.

Compiled regression examples for [2,3,4,5,6] -> [7,9,4] and final [20].

## Failed approaches / repairs

Initial singleton proof supplied the pre-case-split equation where Lean had already rewritten the goal; changed to reflexivity. An implicit round index in rounds_valid did not elaborate; supplied the ceiling logarithm explicitly. The ceiling-division adjunction is a global theorem, not in namespace Nat; corrected that reference. Width multiplication normalization uses ring_nf.

## Remaining obligations

The assignment is NOT complete. Forest leaf-multiset conservation for level and rounds remains unproved. Consequently, no occurrence-preserving permutation to the original input list (including duplicates) has been proved, and the perturbation list has not been transported into original input order. algorithm_leaf_backward_error explicitly refers to the returned tree's leaves; it must not be represented as the full Theorem 3.1 for xs. No vector interface is claimed.

Verification results are recorded below after the final checks. Compilation of partial results is not verification of the complete requested theorem.
