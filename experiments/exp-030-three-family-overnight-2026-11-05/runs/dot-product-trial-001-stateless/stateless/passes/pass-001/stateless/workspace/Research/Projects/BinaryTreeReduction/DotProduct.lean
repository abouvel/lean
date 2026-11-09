import Research.Projects.BinaryTreeReduction.Reduction

/-! # Componentwise backward error for a rounded tree dot product

Each leaf stores a pair of real operands. Multiplication is rounded once at
that leaf, and every internal addition is rounded using the same abstract
model. The reduction shape and all leaf occurrences are preserved.
-/

noncomputable section

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- Exact componentwise products in the original reduction shape. -/
def exactProductTree (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => p.1 * p.2)

/-- Round each componentwise multiplication, preserving the reduction shape. -/
def roundedProductTree (model : Model) (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => model.mul p.1 p.2)

/-- Round each leaf product and then round each addition in the given tree. -/
def roundedDotProduct (model : Model) (tree : Tree (ℝ × ℝ)) : ℝ :=
  roundedSum model (roundedProductTree model tree)

theorem roundedProductTree_isPerturbation (model : Model) (tree : Tree (ℝ × ℝ)) :
    IsPerturbation model.u (exactProductTree tree) (roundedProductTree model tree) := by
  induction tree with
  | leaf p =>
      apply IsPerturbation.leaf
      obtain ⟨δ, hδ, hround⟩ := model.round_spec (p.1 * p.2)
      change |model.round (p.1 * p.2) - p.1 * p.2| ≤ model.u * |p.1 * p.2|
      rw [hround]
      calc
        |p.1 * p.2 * (1 + δ) - p.1 * p.2| = |δ * (p.1 * p.2)| := by
          congr 1
          ring
        _ = |δ| * |p.1 * p.2| := abs_mul _ _
        _ ≤ model.u * |p.1 * p.2| :=
          mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
  | node left right ihLeft ihRight =>
      exact IsPerturbation.node ihLeft ihRight

/-- For every abstract relative-error model and every tree of operand pairs,
the rounded dot product is the exact sum of leafwise perturbations of the
exact products. Each perturbation is bounded relative to its own exact
product by `gamma (tree.depth + 1) model.u`: one multiplication rounding and
at most `tree.depth` addition roundings. `IsPerturbation` also requires the
witness to retain the original tree shape, including every leaf occurrence.
The only additional hypothesis is positivity of the gamma denominator.
-/
theorem roundedDotProduct_exists_perturbation
    (model : Model) (tree : Tree (ℝ × ℝ))
    (hsmall : ((tree.depth + 1 : ℕ) : ℝ) * model.u < 1) :
    ∃ perturbed : Tree ℝ,
      IsPerturbation (gamma (tree.depth + 1) model.u)
        (exactProductTree tree) perturbed ∧
      perturbed.exactSum = roundedDotProduct model tree := by
  have hdepth_small : (tree.depth : ℝ) * model.u < 1 := by
    norm_num at hsmall ⊢
    nlinarith [model.u_nonneg]
  have hrounded_depth : (roundedProductTree model tree).depth = tree.depth := by
    simp [roundedProductTree]
  obtain ⟨perturbed, hperturbed, hsum⟩ :=
    roundedSum_exists_perturbation model (roundedProductTree model tree)
      (by rw [hrounded_depth]; exact hdepth_small)
  rw [hrounded_depth] at hperturbed
  refine ⟨perturbed, ?_, hsum⟩
  apply ((roundedProductTree_isPerturbation model tree).trans hperturbed
    (gamma_nonneg tree.depth model.u model.u_nonneg hdepth_small)).mono
  calc
    model.u + gamma tree.depth model.u * (1 + model.u) =
        gamma tree.depth model.u + model.u * (1 + gamma tree.depth model.u) := by ring
    _ ≤ gamma (tree.depth + 1) model.u :=
      gamma_step tree.depth model.u model.u_nonneg hsmall

end Research.BinaryTreeReduction
