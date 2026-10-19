# Decisions and results

Implemented the original Algorithm 1 and proved Theorem 3.1 in
`/workspace/Research/Submission.lean`, reached by the existing root import
`/workspace/Research.lean`. Neither `/spec` nor project configuration was changed.

## Important decisions

- The numerical implementation is `Bhola.algorithm`, using `roundValues` and
  `stagesValues`. Each stage splits at `ceil(current_length / 2)` and pairs the
  first block with the second at equal offsets. An unmatched entry is returned
  unchanged; no addition with zero is performed. `roundValues_entry` proves
  these branches explicitly.
- A separate expression-tree implementation is proved equivalent to the
  numerical loop. List permutations preserve multiplicities, including repeated
  and zero inputs. Perturbations are transported back into the original order
  and indexed by `Fin xs.length`.
- `depth n = Nat.clog 2 n` is the exact integer ceiling logarithm. Stage sizes
  are proved to be `ceil(n / 2^ℓ)`, and `stage_offset` connects the recursive
  splitting rule to the paper's original global offset. The final tree's height
  is proved equal to this depth, not merely bounded above by it.
- The main theorem assumes nonempty arbitrary real inputs, nonnegative unit
  roundoff, `depth * u < 1`, and the relative-error model only at the actual
  additions of this execution (`ExecutionModel`). A corollary accepts a total
  deterministic addition function satisfying the model universally. As in the
  paper, absence of overflow/underflow is represented by validity of the
  relative-error equations, rather than a bit-level IEEE implementation.
- Instead of introducing path products, the proof propagates one perturbation
  per leaf through each rounded addition. The fully proved recurrence
  `gamma d u * (1 + u) + u ≤ gamma (d + 1) u` gives exactly the paper's
  `gamma d u = d*u/(1-d*u)` bound.

## Failed approaches, resolved

An initial direct denominator-clearing tactic for the gamma recurrence produced
an unsuitable goal. Normalizing the left side to
`((d+1)*u)/(1-d*u)` made denominator monotonicity sufficient. Some initial
library-lemma names and indexing syntax were incorrect; these were corrected.
The first root-build attempt also exposed a missing explicit `Tree` type on an
existential binder in the additional numerical specification; this was fixed
before the successful build. No failed approach remains in the submission.

## Completed and verified

- `Bhola.theorem_3_1`: computed result is the sum of `x_i + Δ_i`, with
  `|Δ_i| ≤ gamma(depth n,u) * |x_i|` for every original input occurrence.
- `Bhola.algorithm1_spec` and `algorithm_tree_spec`: singleton final result,
  preservation of all input occurrences, and exact logarithmic tree depth.
- `stagesValues_length`, `stage_offset`, and `roundValues_entry`: original
  schedule, offsets, and unchanged carry branch.
- `algorithm_exact`: exact arithmetic yields the original list sum.

Validation: `lake env lean Research/Submission.lean` and the full root
`lake build` both completed successfully with no warnings in the final version.
An independent `import Research` audit checked the central declarations;
`#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`.
There are no `sorry`, admitted obligations, or custom axioms.

Remaining obligations: none for the assigned abstract floating-point model.
