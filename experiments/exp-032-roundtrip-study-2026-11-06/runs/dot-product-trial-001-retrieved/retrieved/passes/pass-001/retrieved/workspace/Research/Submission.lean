import Research.Projects.BinaryTreeReduction.Reduction

/-!
# Rounded tree dot product

The products at the leaves are rounded once, then the supplied rounded tree
reduction rounds each internal addition. The target theorem expresses this
computation as the exact sum of leafwise perturbations of the exact products.
-/

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- Exact componentwise products, retaining each leaf occurrence and tree shape. -/
noncomputable def exactProductTree (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => p.1 * p.2)

/-- One rounded multiplication at each leaf of the input tree. -/
def roundedProductTree (model : Model) (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => model.mul p.1 p.2)

/-- Rounded leaf products followed by rounded addition at every internal node. -/
def roundedDotProduct (model : Model) (tree : Tree (ℝ × ℝ)) : ℝ :=
  roundedSum model (roundedProductTree model tree)

@[simp] theorem exactProductTree_depth (tree : Tree (ℝ × ℝ)) :
    (exactProductTree tree).depth = tree.depth := by
  exact Tree.depth_map _ tree

@[simp] theorem roundedProductTree_depth (model : Model) (tree : Tree (ℝ × ℝ)) :
    (roundedProductTree model tree).depth = tree.depth := by
  exact Tree.depth_map _ tree

/-- Rounding each product gives a leafwise perturbation bounded by `u`. -/
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

/-- For every relative-error model and pair tree, the rounded dot product is
the exact sum of leafwise perturbations of the exact products. Each leaf incurs
one multiplication rounding and at most `tree.depth` addition roundings.
The supplied model includes nonnegative unit roundoff and the relative-error
specification for every rounded operation; the only additional assumption is
the displayed smallness condition. -/
theorem roundedDotProduct_exists_perturbation
    (model : Model) (tree : Tree (ℝ × ℝ))
    (hsmall : ((tree.depth + 1 : ℕ) : ℝ) * model.u < 1) :
    ∃ perturbed : Tree ℝ,
      IsPerturbation (gamma (tree.depth + 1) model.u)
        (exactProductTree tree) perturbed ∧
      perturbed.exactSum = roundedDotProduct model tree := by
  have hdepth_small : (tree.depth : ℝ) * model.u < 1 := by
    push_cast at hsmall
    nlinarith [model.u_nonneg]
  obtain ⟨perturbed, hperturbed, hsum⟩ :=
    roundedSum_exists_perturbation model (roundedProductTree model tree)
      (by simpa using hdepth_small)
  rw [roundedProductTree_depth] at hperturbed
  have hcomposed := (roundedProductTree_isPerturbation model tree).trans hperturbed
    (gamma_nonneg tree.depth model.u model.u_nonneg hdepth_small)
  refine ⟨perturbed, hcomposed.mono ?_, hsum⟩
  calc
    model.u + gamma tree.depth model.u * (1 + model.u) =
        gamma tree.depth model.u + model.u * (1 + gamma tree.depth model.u) := by ring
    _ ≤ gamma (tree.depth + 1) model.u :=
      gamma_step tree.depth model.u model.u_nonneg hsmall

end Research.BinaryTreeReduction
