import Research.Projects.BinaryTreeReduction.Reduction

/-!
# Componentwise backward error of a rounded tree dot product

The leaves contain pairs of real inputs. Each pair is multiplied with one
rounding, and the resulting values are reduced using rounded tree addition.
The depth counts addition roundings; the extra one accounts for multiplication.

Statement revision record: initial statement from `/spec/source.txt`.
No `/spec/feedback.json` was present, and no statement revision was required.
-/

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- The exact componentwise products, retaining the input reduction shape. -/
def exactProductTree (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun pair => pair.1 * pair.2)

/-- Round each componentwise multiplication before reducing the tree. -/
def roundedProductTree (model : Model) (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun pair => model.mul pair.1 pair.2)

/-- The dot product evaluated with rounded products and rounded tree addition. -/
def roundedDotProduct (model : Model) (tree : Tree (ℝ × ℝ)) : ℝ :=
  roundedSum model (roundedProductTree model tree)

/-- Rounding each product gives a leafwise relative perturbation. -/
theorem roundedProductTree_isPerturbation (model : Model)
    (tree : Tree (ℝ × ℝ)) :
    IsPerturbation model.u (exactProductTree tree)
      (roundedProductTree model tree) := by
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

/-- For every abstract relative-error model and every binary tree of input
pairs, the rounded dot product is the exact sum of a tree of perturbed exact
products. The leafwise relative bound accounts for one multiplication and at
most `tree.depth` additions. `IsPerturbation` also preserves the tree shape,
including leaves whose exact product is zero.
-/
theorem roundedDotProduct_exists_perturbation
    (model : Model) (tree : Tree (ℝ × ℝ))
    (hsmall : ((tree.depth + 1 : ℕ) : ℝ) * model.u < 1) :
    ∃ perturbed : Tree ℝ,
      IsPerturbation (gamma (tree.depth + 1) model.u)
        (exactProductTree tree) perturbed ∧
      perturbed.exactSum = roundedDotProduct model tree := by
  have hdepthSmall : (tree.depth : ℝ) * model.u < 1 := by
    push_cast at hsmall
    nlinarith [model.u_nonneg]
  obtain ⟨perturbed, hperturbed, hsum⟩ :=
    roundedSum_exists_perturbation_of_depth_le model tree.depth
      (roundedProductTree model tree)
      (by simp [roundedProductTree]) hdepthSmall
  refine ⟨perturbed, ?_, hsum⟩
  have hcomposed := (roundedProductTree_isPerturbation model tree).trans
    hperturbed (gamma_nonneg tree.depth model.u model.u_nonneg hdepthSmall)
  apply hcomposed.mono
  calc
    model.u + gamma tree.depth model.u * (1 + model.u) =
        gamma tree.depth model.u + model.u * (1 + gamma tree.depth model.u) := by
      ring
    _ ≤ gamma (tree.depth + 1) model.u :=
      gamma_step tree.depth model.u model.u_nonneg hsmall

end Research.BinaryTreeReduction
