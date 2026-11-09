import Research.Projects.BinaryTreeReduction.Reduction

/-!
# Rounded dot products on arbitrary binary trees

The constructions perform one rounded multiplication at each leaf and then
one rounded addition at each internal node. The target includes both sources
of error, relative to the exact componentwise products.

Statement audit: follows /spec/source.txt. No /spec/feedback.json was supplied;
there is no feedback-driven revision. The final proof is left to the proof role.
-/

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- Exact componentwise products, preserving the input reduction tree. -/
def exactProductTree (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => p.1 * p.2)

/-- One rounded multiplication of the two components at every leaf. -/
def roundedProductTree (model : Model) (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => model.mul p.1 p.2)

/-- Reduce the rounded componentwise products using rounded tree addition. -/
def roundedDotProduct (model : Model) (tree : Tree (ℝ × ℝ)) : ℝ :=
  roundedSum model (roundedProductTree model tree)

/-- The rounded dot product is the exact sum of a tree of leafwise
perturbations of the exact products. Each leaf has relative error bounded by
`gamma (tree.depth + 1) model.u`: one error for its multiplication and at most
`tree.depth` errors for its additions. `IsPerturbation` also preserves the
shape and multiplicity of all leaf occurrences, including zero products.
-/
theorem roundedDotProduct_exists_perturbation
    (model : Model) (tree : Tree (ℝ × ℝ))
    (hsmall : ((tree.depth + 1 : ℕ) : ℝ) * model.u < 1) :
    ∃ perturbed : Tree ℝ,
      IsPerturbation (gamma (tree.depth + 1) model.u)
        (exactProductTree tree) perturbed ∧
      perturbed.exactSum = roundedDotProduct model tree := by
  have hmul : IsPerturbation model.u
      (exactProductTree tree) (roundedProductTree model tree) := by
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
  have htail : (tree.depth : ℝ) * model.u < 1 := by
    norm_num at hsmall ⊢
    nlinarith [model.u_nonneg]
  obtain ⟨perturbed, hadd, hsum⟩ :=
    roundedSum_exists_perturbation model (roundedProductTree model tree)
      (by simpa only [hdepth] using htail)
  rw [hdepth] at hadd
  refine ⟨perturbed, ?_, hsum⟩
  apply (hmul.trans hadd (gamma_nonneg tree.depth model.u model.u_nonneg htail)).mono
  calc
    model.u + gamma tree.depth model.u * (1 + model.u) =
        gamma tree.depth model.u + model.u * (1 + gamma tree.depth model.u) := by ring
    _ ≤ gamma (tree.depth + 1) model.u :=
      gamma_step tree.depth model.u model.u_nonneg hsmall

end Research.BinaryTreeReduction
