# Run 001 - accumulated error and arbitrary-tree reduction

## Objective

Formalize the reusable accumulated relative-error bound, prove backward
stability for an arbitrary binary reduction tree, and extend it to rounded
componentwise products.

## Prompt and approach

The user asked to implement the staged verification plan for the binary-tree
proof. The proof was divided into independent layers:

1. finite products of factors `(1 + δ)`;
2. leafwise perturbations for a reduction tree;
3. induction on a depth budget;
4. one extra error for each rounded componentwise product.

Aristotle was not used in this run. This gives a manually verified baseline
for later cost and success-rate comparisons.

## What worked

- An induction on a list of errors proves the `gamma` product bound.
- Induction on a depth budget avoids explicit path-index bookkeeping.
- A same-shape `IsPerturbation` relation expresses backward error directly.
- Composing multiplication and summation perturbations gives a
  `gamma (depth + 1)` deterministic dot-product bound.

## What did not work initially

- Compiling a dependent module before rebuilding changed imports loaded stale
  `.olean` files. Rebuilding the dependencies first fixed this.
- The first algebraic proof of `gamma_step` asked nonlinear arithmetic to
  reason directly about division. Rewriting both sides over positive
  denominators made the ordering argument explicit.
- The triangle-inequality lemma is named `abs_add_le`, not `abs_add`, in this
  Lean/Mathlib version.

## Reasoning behind decisions

- The floating-point model remains abstract instead of modeling IEEE 754 bits.
- No rounding operation is added when a value is merely carried to a higher
  conceptual level. Short paths are covered by the `depth ≤ k` theorem.
- The balanced-tree constructor is kept separate from numerical error analysis.
  This makes the error theorem reusable and isolates the remaining algorithmic
  proof about `Nat.clog 2 n`.

## Observations

- The deterministic PDF theorem and the probabilistic dot-product theorem in
  the screenshot are distinct targets.
- The arbitrary-tree theorem is stronger as an interface: any construction
  with a verified depth bound can use it.
- The remaining source-specific gap is the proof that the pseudocode builds a
  tree of depth at most `⌈log₂ n⌉` for every nonempty input.

## Verification

- Full project build: passed.
- Four-leaf tree depth: verified as `2`.
- Four-leaf exact sum for `2, 3, 4, 5`: verified as `14`.
- `sorry`, `admit`, and custom-axiom scan: required before final handoff.
