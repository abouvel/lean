import Research.Projects.BinaryTreeReduction.Reduction

/-!
# Rounded dot products on binary reduction trees

The statement follows `/spec/source.txt`. Each leaf incurs one multiplication
rounding, and each leaf-to-root path incurs at most `tree.depth` addition
roundings. The supplied prerequisite modules are copied unchanged.

Statement revision record: this is the initial statement; no feedback file was
present and no prior statement was revised.
-/

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

noncomputable section

/-- The exact componentwise products, retaining the input reduction shape. -/
def exactProductTree (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => p.1 * p.2)

/-- Round each componentwise product, retaining the input reduction shape. -/
def roundedProductTree (model : Model) (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => model.mul p.1 p.2)

/-- Round the products and then perform rounded addition along the given tree. -/
def roundedDotProduct (model : Model) (tree : Tree (ℝ × ℝ)) : ℝ :=
  roundedSum model (roundedProductTree model tree)

@[simp] theorem depth_exactProductTree (tree : Tree (ℝ × ℝ)) :
    (exactProductTree tree).depth = tree.depth := by
  exact Tree.depth_map _ tree

@[simp] theorem depth_roundedProductTree (model : Model) (tree : Tree (ℝ × ℝ)) :
    (roundedProductTree model tree).depth = tree.depth := by
  exact Tree.depth_map _ tree

/-- Each product incurs at most one relative rounding error. -/
theorem productTree_isPerturbation (model : Model) (tree : Tree (ℝ × ℝ)) :
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

/-- For every abstract relative-error model and every binary tree of pairs,
the rounded dot product is the exact sum of a same-shape tree of perturbed
exact products. The bound accounts for the multiplication at each leaf and
all additions on its path to the root, including the single-leaf case.

The only additional hypothesis is `(depth + 1) * u < 1`; nonnegativity of `u`
and the rounding specification are fields of the supplied `Model`.
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
  rw [depth_roundedProductTree] at hperturbed
  refine ⟨perturbed, ?_, hsum⟩
  have hcomposed := (productTree_isPerturbation model tree).trans hperturbed
    (gamma_nonneg tree.depth model.u model.u_nonneg hdepth_small)
  apply hcomposed.mono
  calc
    model.u + gamma tree.depth model.u * (1 + model.u) =
        gamma tree.depth model.u + model.u * (1 + gamma tree.depth model.u) := by ring
    _ ≤ gamma (tree.depth + 1) model.u :=
      gamma_step tree.depth model.u model.u_nonneg hsmall

end

end Research.BinaryTreeReduction
