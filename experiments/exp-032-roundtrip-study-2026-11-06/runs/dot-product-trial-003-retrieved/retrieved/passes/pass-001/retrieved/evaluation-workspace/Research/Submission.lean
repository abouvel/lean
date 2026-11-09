import Research.Projects.BinaryTreeReduction.Reduction

/-!
# Componentwise backward error for a rounded tree dot product

Each pair at a leaf contributes one rounded multiplication. Internal nodes
then use the supplied rounded addition reduction. The error bound counts that
multiplication and at most `tree.depth` additions on each leaf-to-root path.
-/

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- Exact componentwise products, retaining the input tree's binary shape. -/
def exactProductTree (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun pair => pair.1 * pair.2)

/-- Round every componentwise product under the given relative-error model. -/
def roundedProductTree (model : Model) (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun pair => model.mul pair.1 pair.2)

/-- Compute rounded products and reduce them with rounded tree addition. -/
def roundedDotProduct (model : Model) (tree : Tree (ℝ × ℝ)) : ℝ :=
  roundedSum model (roundedProductTree model tree)

@[simp] theorem exactProductTree_depth (tree : Tree (ℝ × ℝ)) :
    (exactProductTree tree).depth = tree.depth := by
  simp [exactProductTree]

@[simp] theorem roundedProductTree_depth (model : Model) (tree : Tree (ℝ × ℝ)) :
    (roundedProductTree model tree).depth = tree.depth := by
  simp [roundedProductTree]

/-- For every model and binary tree, the rounded dot product is the exact sum
of leafwise perturbations of the exact products. The bound includes one
multiplication rounding and all addition roundings along each leaf's path.
No exact-arithmetic assumption is imposed on the model. -/
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
    | leaf pair =>
        apply IsPerturbation.leaf
        obtain ⟨δ, hδ, hround⟩ := model.round_spec (pair.1 * pair.2)
        change |model.round (pair.1 * pair.2) - pair.1 * pair.2| ≤
          model.u * |pair.1 * pair.2|
        rw [hround]
        calc
          |pair.1 * pair.2 * (1 + δ) - pair.1 * pair.2| =
              |δ| * |pair.1 * pair.2| := by
                rw [← abs_mul]
                congr 1
                ring
          _ ≤ model.u * |pair.1 * pair.2| :=
            mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
    | node left right ihLeft ihRight =>
        exact IsPerturbation.node ihLeft ihRight
  have hdepth_small : (tree.depth : ℝ) * model.u < 1 := by
    push_cast at hsmall
    nlinarith [model.u_nonneg]
  obtain ⟨perturbed, hadd, hsum⟩ :=
    roundedSum_exists_perturbation model (roundedProductTree model tree)
      (by simpa using hdepth_small)
  simp only [roundedProductTree_depth] at hadd
  refine ⟨perturbed, ?_, hsum⟩
  apply (hmul.trans hadd
    (gamma_nonneg tree.depth model.u model.u_nonneg hdepth_small)).mono
  calc
    model.u + gamma tree.depth model.u * (1 + model.u) =
        gamma tree.depth model.u + model.u * (1 + gamma tree.depth model.u) := by ring
    _ ≤ gamma (tree.depth + 1) model.u :=
      gamma_step tree.depth model.u model.u_nonneg hsmall

end Research.BinaryTreeReduction
