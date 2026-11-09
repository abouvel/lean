import Research.Projects.BinaryTreeReduction.Reduction

/-! # Floating-point dot product -/

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- One rounded componentwise product before tree reduction. -/
def roundedProductTerm (model : Model) (x y : ℝ) : ℝ :=
  model.mul x y

/-- Exact componentwise products stored in the leaves of the reduction tree. -/
def exactProductTree (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map fun pair => pair.1 * pair.2

/-- Rounded componentwise products stored in the same reduction shape. -/
def roundedProductTree (model : Model) (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map fun pair => roundedProductTerm model pair.1 pair.2

/-- Compute a dot product by rounding every product and then reducing those
products with rounded binary-tree addition. -/
def roundedDotProduct (model : Model) (tree : Tree (ℝ × ℝ)) : ℝ :=
  roundedSum model (roundedProductTree model tree)

/-- Rounding each componentwise product perturbs its exact value by at most
one unit roundoff. -/
theorem roundedProductTree_isPerturbation (model : Model)
    (tree : Tree (ℝ × ℝ)) :
    IsPerturbation model.u (exactProductTree tree) (roundedProductTree model tree) := by
  induction tree with
  | leaf pair =>
      rcases pair with ⟨x, y⟩
      obtain ⟨δ, hδ, hround⟩ := model.round_spec (x * y)
      apply IsPerturbation.leaf
      simp only [roundedProductTerm, Model.mul]
      rw [hround]
      calc
        |x * y * (1 + δ) - x * y| = |δ| * |x * y| := by
          rw [show x * y * (1 + δ) - x * y = δ * (x * y) by ring, abs_mul]
        _ ≤ model.u * |x * y| :=
          mul_le_mul_of_nonneg_right hδ (abs_nonneg (x * y))
  | node left right ihLeft ihRight =>
      exact IsPerturbation.node ihLeft ihRight


/-- The requested claim is stated but not proved. -/
def DotProductBackwardErrorClaim (model : Model) (tree : Tree (ℝ × ℝ)) : Prop :=
  ((tree.depth + 1 : ℕ) : ℝ) * model.u < 1 →
    ∃ perturbed : Tree ℝ,
      IsPerturbation (gamma (tree.depth + 1) model.u)
        (exactProductTree tree) perturbed ∧
      perturbed.exactSum = roundedDotProduct model tree

end Research.BinaryTreeReduction
