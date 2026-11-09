import Research.Projects.BinaryTreeReduction.Reduction

/-!
# Floating-point dot products on arbitrary binary trees

Each leaf multiplication is rounded once, and every internal addition is
rounded using the same abstract relative-error model.
-/

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- Exact componentwise products, preserving the input tree's shape and
each occurrence of a leaf. -/
def exactProductTree (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => p.1 * p.2)

/-- Componentwise products rounded once at each leaf. -/
def roundedProductTree (model : Model) (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => model.mul p.1 p.2)

/-- Round each leaf product, then reduce with rounded tree addition. -/
def roundedDotProduct (model : Model) (tree : Tree (ℝ × ℝ)) : ℝ :=
  roundedSum model (roundedProductTree model tree)

/-- For every abstract relative-error model and every tree of real pairs,
the rounded dot product is the exact sum of leafwise perturbations of the
exact products. The bound counts one multiplication and at most `tree.depth`
additions per leaf, including zero products and repeated leaf values. -/
theorem roundedDotProduct_exists_perturbation
    (model : Model) (tree : Tree (ℝ × ℝ))
    (hsmall : ((tree.depth + 1 : ℕ) : ℝ) * model.u < 1) :
    ∃ perturbed : Tree ℝ,
      IsPerturbation (gamma (tree.depth + 1) model.u)
        (exactProductTree tree) perturbed ∧
      perturbed.exactSum = roundedDotProduct model tree := by
  have hmul : IsPerturbation model.u (exactProductTree tree)
      (roundedProductTree model tree) := by
    clear hsmall
    induction tree with
    | leaf p =>
        apply IsPerturbation.leaf
        obtain ⟨δ, hδ, hround⟩ := model.round_spec (p.1 * p.2)
        change |model.round (p.1 * p.2) - p.1 * p.2| ≤
          model.u * |p.1 * p.2|
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
  have hdepth : (roundedProductTree model tree).depth = tree.depth := by
    simp [roundedProductTree]
  have hsmall' : (tree.depth : ℝ) * model.u < 1 := by
    norm_num at hsmall ⊢
    nlinarith [model.u_nonneg]
  obtain ⟨perturbed, hadd, hsum⟩ := roundedSum_exists_perturbation model
    (roundedProductTree model tree) (by rw [hdepth]; exact hsmall')
  rw [hdepth] at hadd
  refine ⟨perturbed, ?_, hsum⟩
  apply (hmul.trans hadd (gamma_nonneg tree.depth model.u model.u_nonneg hsmall')).mono
  calc
    model.u + gamma tree.depth model.u * (1 + model.u) =
        gamma tree.depth model.u + model.u * (1 + gamma tree.depth model.u) := by ring
    _ ≤ gamma (tree.depth + 1) model.u :=
      gamma_step tree.depth model.u model.u_nonneg hsmall

end Research.BinaryTreeReduction
