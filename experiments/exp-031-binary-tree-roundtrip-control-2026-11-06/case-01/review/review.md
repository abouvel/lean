# Review: pass

The candidate proves Theorem 3.1 in `Research/Submission.lean:391–408`, with perturbations indexed by every original input occurrence. Its assumptions are nonempty input, nonnegative roundoff, the standard relative-error model at executed additions, and ceil(log2 n)*u < 1. These do not assume the conclusion.

The numerical implementation uses the required ceiling-half offset, carries unmatched subtrees without extra arithmetic, preserves multiplicities, and has exactly ceil(log2 n) tree height. The final bound uses d*u/(1-d*u) for each occurrence. The real-valued result applies separately to each component.

Offline verification reports a successful build without proof placeholders or custom axioms. Independent recompilation of the current source also succeeded. `IndependentChecks.lean` compiled successfully: it checks the complete acceptance trace, singleton behavior, duplicate inputs, odd-length carries with a deliberately inexact operation, and a nonvacuous exact-addition instantiation of the target. Printed theorem axioms are only Lean's standard propext, Classical.choice and Quot.sound.

The model abstracts floating-point execution through local relative-error equations; it does not implement a hardware format. No missing mathematical obligations were found. See `review.json` for requirement-by-requirement evidence.
