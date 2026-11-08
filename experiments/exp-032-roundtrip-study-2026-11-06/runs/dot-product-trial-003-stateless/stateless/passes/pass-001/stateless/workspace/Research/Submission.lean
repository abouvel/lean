import Research.Projects.BinaryTreeReduction.Reduction

/-!
# Componentwise backward error for a rounded tree dot product

The three constructions preserve every leaf occurrence and the supplied tree's
reduction shape. Multiplications are rounded at leaves, and additions are rounded
at internal nodes using the same arbitrary relative-error model.

Statement review: no `/spec/feedback.json` was present. The statement below
directly follows `/spec/source.txt`; no statement revision or weakening was made.
-/

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- Exact componentwise products, retaining the original reduction shape. -/
def exactProductTree (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => p.1 * p.2)

/-- Round each componentwise product using the supplied relative-error model. -/
def roundedProductTree (model : Model) (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => model.mul p.1 p.2)

/-- Round each product, then round every internal addition in the given tree. -/
def roundedDotProduct (model : Model) (tree : Tree (ℝ × ℝ)) : ℝ :=
  roundedSum model (roundedProductTree model tree)

@[simp] theorem exactProductTree_depth (tree : Tree (ℝ × ℝ)) :
    (exactProductTree tree).depth = tree.depth := by
  simp [exactProductTree]

@[simp] theorem roundedProductTree_depth (model : Model) (tree : Tree (ℝ × ℝ)) :
    (roundedProductTree model tree).depth = tree.depth := by
  simp [roundedProductTree]

/-- For every relative-error model and every binary tree of input pairs, the
rounded dot product is the exact sum of leafwise perturbations of the exact
products. Each leaf's relative perturbation is bounded by `gamma (depth + 1) u`,
accounting for one multiplication and at most `depth` additions.

`IsPerturbation` enforces matching tree shape and the bound separately at every
leaf, including repeated and zero products. The model's relative-error contract
is part of `Model`; the only additional hypothesis is the stated smallness bound.
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
  have hdepth_small : (tree.depth : ℝ) * model.u < 1 := by
    norm_num at hsmall ⊢
    nlinarith [model.u_nonneg]
  obtain ⟨perturbed, hperturbed, hsum⟩ :=
    roundedSum_exists_perturbation model (roundedProductTree model tree)
      (by simpa using hdepth_small)
  rw [roundedProductTree_depth] at hperturbed
  refine ⟨perturbed, ?_, hsum⟩
  apply (hmul.trans hperturbed
    (gamma_nonneg tree.depth model.u model.u_nonneg hdepth_small)).mono
  calc
    model.u + gamma tree.depth model.u * (1 + model.u) =
        gamma tree.depth model.u + model.u * (1 + gamma tree.depth model.u) := by
          ring
    _ ≤ gamma (tree.depth + 1) model.u :=
      gamma_step tree.depth model.u model.u_nonneg hsmall

end Research.BinaryTreeReduction
