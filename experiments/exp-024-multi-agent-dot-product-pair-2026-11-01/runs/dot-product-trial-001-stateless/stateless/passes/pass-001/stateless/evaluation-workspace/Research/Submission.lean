import Research.Projects.BinaryTreeReduction.Reduction

/-!
# Floating-point dot product on a binary reduction tree

Statement follows /spec/source.txt. No /spec/feedback.json was present;
no statement revision was required.
-/

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- The exact componentwise products, with the original reduction shape. -/
def exactProductTree (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => p.1 * p.2)

/-- Round each componentwise product using the supplied model. -/
def roundedProductTree (model : Model) (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => model.mul p.1 p.2)

/-- Round each product, then reduce using rounded addition at every internal node. -/
def roundedDotProduct (model : Model) (tree : Tree (ℝ × ℝ)) : ℝ :=
  roundedSum model (roundedProductTree model tree)

@[simp] theorem exactProductTree_depth (tree : Tree (ℝ × ℝ)) :
    (exactProductTree tree).depth = tree.depth := by
  simp [exactProductTree]

@[simp] theorem roundedProductTree_depth (model : Model) (tree : Tree (ℝ × ℝ)) :
    (roundedProductTree model tree).depth = tree.depth := by
  simp [roundedProductTree]

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

/-- For every relative-error model and every binary tree of real pairs,
rounding the products and the reduction additions gives the exact sum of a
same-shaped tree of perturbed exact products. Every leaf has relative error
at most `gamma (tree.depth + 1) model.u`: one multiplication and at most
`tree.depth` additions. The only additional assumption is the stated smallness
condition; nonnegativity of `u` and the rounding specification belong to `Model`.
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
  obtain ⟨perturbed, hperturbed, hsum⟩ :=
    roundedSum_exists_perturbation model (roundedProductTree model tree)
      (by simpa using hdepth_small)
  rw [roundedProductTree_depth] at hperturbed
  refine ⟨perturbed, ?_, hsum⟩
  have hcomposed := (roundedProductTree_isPerturbation model tree).trans hperturbed
    (gamma_nonneg tree.depth model.u model.u_nonneg hdepth_small)
  apply hcomposed.mono
  calc
    model.u + gamma tree.depth model.u * (1 + model.u) =
        gamma tree.depth model.u + model.u * (1 + gamma tree.depth model.u) := by ring
    _ ≤ gamma (tree.depth + 1) model.u :=
      gamma_step tree.depth model.u model.u_nonneg hsmall

end Research.BinaryTreeReduction
