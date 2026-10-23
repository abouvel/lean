Implemented a compiling partial formalization in [Submission.lean](/workspace/Research/Submission.lean), connected to the root import.

Proved logarithmic termination, exact-arithmetic correctness, and occurrence-label conservation. `lake build` passes.

**Theorem 3.1 remains incomplete:** the global componentwise backward-error bound is unproved. Remaining obligations are recorded in [decisions.md](/output/decisions.md); memory usage is recorded in [retrieval.md](/output/retrieval.md).