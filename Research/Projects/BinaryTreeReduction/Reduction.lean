import Research.Common.FloatingPoint.Gamma
import Research.Projects.BinaryTreeReduction.Tree

/-! # Floating-point binary-tree reduction -/

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- Evaluate a tree using floating-point addition at every internal node. -/
def roundedSum (model : Model) : Tree ℝ → ℝ
  | .leaf value => value
  | .node left right => model.add (roundedSum model left) (roundedSum model right)

/-!
Proof steps:

1. Express each leaf as its value times the rounding factors on its path.
2. Bound the number of factors by the tree depth.
3. Build a balanced tree for arbitrary input length and prove depth `≤ ⌈log₂ n⌉`.
4. Apply the `gamma` bound to obtain
   `ŷ = ∑ i, (x i + Δx i)` and
   `|Δx i| ≤ gamma (⌈log₂ n⌉) model.u * |x i|`.

The final result must support non-power-of-two input lengths.
-/

end Research.BinaryTreeReduction
