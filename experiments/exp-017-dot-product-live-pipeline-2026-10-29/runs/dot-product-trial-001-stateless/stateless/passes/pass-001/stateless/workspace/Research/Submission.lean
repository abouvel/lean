import Research.Projects.BinaryTreeReduction.Reduction

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- Exact componentwise products, with the input reduction shape. -/
def exactProductTree (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => p.1 * p.2)

/-- Each multiplication is rounded once before any additions. -/
def roundedProductTree (model : Model) (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => model.mul p.1 p.2)

/-- Rounded multiplication followed by rounded addition along the tree. -/
def roundedDotProduct (model : Model) (tree : Tree (ℝ × ℝ)) : ℝ :=
  roundedSum model (roundedProductTree model tree)

/-- The multiplication stage incurs a componentwise relative error at most `u`. -/
theorem roundedProductTree_isPerturbation (model : Model)
    (tree : Tree (ℝ × ℝ)) :
    IsPerturbation model.u (exactProductTree tree) (roundedProductTree model tree) := by
  induction tree with
  | leaf p =>
      apply IsPerturbation.leaf
      obtain ⟨δ, hδ, hr⟩ := model.round_spec (p.1 * p.2)
      change |model.round (p.1 * p.2) - p.1 * p.2| ≤ model.u * |p.1 * p.2|
      rw [hr]
      calc
        |p.1 * p.2 * (1 + δ) - p.1 * p.2| = |δ * (p.1 * p.2)| := by
          congr 1
          ring
        _ = |δ| * |p.1 * p.2| := abs_mul _ _
        _ ≤ model.u * |p.1 * p.2| :=
          mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
  | node left right ihLeft ihRight =>
      exact IsPerturbation.node ihLeft ihRight

/-- Full componentwise backward error for every model and pair tree: one
multiplication and at most `depth` additions affect each exact product. -/
theorem roundedDotProduct_exists_perturbation
    (model : Model) (tree : Tree (ℝ × ℝ))
    (hsmall : ((tree.depth + 1 : ℕ) : ℝ) * model.u < 1) :
    ∃ perturbed : Tree ℝ,
      IsPerturbation (gamma (tree.depth + 1) model.u)
        (exactProductTree tree) perturbed ∧
      perturbed.exactSum = roundedDotProduct model tree := by
  have htail : (tree.depth : ℝ) * model.u < 1 := by
    norm_num at hsmall ⊢
    nlinarith [model.u_nonneg]
  have hdepth : (roundedProductTree model tree).depth = tree.depth := by
    simp [roundedProductTree]
  obtain ⟨perturbed, hp, hs⟩ := roundedSum_exists_perturbation model
    (roundedProductTree model tree) (by rw [hdepth]; exact htail)
  rw [hdepth] at hp
  refine ⟨perturbed, ?_, hs⟩
  have hcompose := (roundedProductTree_isPerturbation model tree).trans hp
    (gamma_nonneg tree.depth model.u model.u_nonneg htail)
  apply hcompose.mono
  calc
    model.u + gamma tree.depth model.u * (1 + model.u) =
        gamma tree.depth model.u + model.u * (1 + gamma tree.depth model.u) := by ring
    _ ≤ gamma (tree.depth + 1) model.u :=
      gamma_step tree.depth model.u model.u_nonneg hsmall

end Research.BinaryTreeReduction
