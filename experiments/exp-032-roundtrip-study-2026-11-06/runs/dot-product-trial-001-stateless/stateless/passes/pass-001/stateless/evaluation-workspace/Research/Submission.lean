import Research.Projects.BinaryTreeReduction.Reduction

/-!
# Componentwise backward error for a tree dot product

The statement follows `/spec/source.txt`. No `/spec/feedback.json` was present;
this is the initial statement, with no revisions to the requested conclusion.
The proof combines multiplication and tree-addition perturbations.
-/

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- Exact componentwise products, retaining every leaf occurrence and the
original reduction shape. -/
def exactProductTree (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => p.1 * p.2)

/-- Round each componentwise product once, retaining the reduction shape. -/
def roundedProductTree (model : Model) (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => model.mul p.1 p.2)

/-- Multiply with rounding at each leaf, then add with rounding at each
internal node. A leaf tree incurs only its multiplication rounding. -/
def roundedDotProduct (model : Model) (tree : Tree (ℝ × ℝ)) : ℝ :=
  roundedSum model (roundedProductTree model tree)

/-- For every relative-error model and every binary tree of input pairs, the
rounded dot product is the exact sum of a tree of leafwise perturbations of
the exact products. The bound accounts for one multiplication and at most
`tree.depth` additions per leaf, including for unbalanced trees and zero products.
`IsPerturbation` preserves shape and bounds each leaf's absolute change by
`gamma (tree.depth + 1) model.u` times the absolute exact leaf product. -/
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
  have hdepth : (tree.depth : ℝ) * model.u < 1 := by
    norm_num at hsmall ⊢
    nlinarith [model.u_nonneg]
  obtain ⟨perturbed, hadd, hsum⟩ :=
    roundedSum_exists_perturbation model (roundedProductTree model tree)
      (by simpa [roundedProductTree] using hdepth)
  have hadd' : IsPerturbation (gamma tree.depth model.u)
      (roundedProductTree model tree) perturbed := by
    simpa [roundedProductTree] using hadd
  refine ⟨perturbed, ?_, hsum⟩
  apply (hmul.trans hadd'
    (gamma_nonneg tree.depth model.u model.u_nonneg hdepth)).mono
  calc
    model.u + gamma tree.depth model.u * (1 + model.u) =
        gamma tree.depth model.u + model.u * (1 + gamma tree.depth model.u) := by
      ring
    _ ≤ gamma (tree.depth + 1) model.u :=
      gamma_step tree.depth model.u model.u_nonneg hsmall

end Research.BinaryTreeReduction
