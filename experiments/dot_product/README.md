# Dot product pipeline experiment

## Objective

Convert a fixed Lean statement of dot-product symmetry into a machine-checked proof.

## Pipeline organization

1. A human fixes the mathematical meaning in `Research/DotProduct.lean`.
2. Lean checks that the statement and definitions elaborate.
3. A minimal submission project is created in `submission/`. It contains no credentials.
4. Aristotle receives only that staging project and the recorded prompt in `prompt.txt`.
5. The returned proof is built locally with Lean.
6. The run record captures the outcome, decisions, and observations.

## Success criteria

- `lake build` succeeds.
- No `sorry` or `admit` remains in the returned proof.
- Aristotle does not change the definition or theorem statement.
- The final statement still expresses symmetry of the real dot product.

## Baselines for later comparison

- Direct Aristotle submission with no decomposition.
- Local cheap tactics before an Aristotle call.
- A decomposed proof with one lemma per subgoal.
- A memory-assisted run that can reuse patterns learned on earlier tasks.
