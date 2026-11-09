import Research.Projects.BinaryTreeReduction.Reduction

/-!
# Rounded dot product on an arbitrary binary reduction tree

Products are rounded once at every leaf; additions are rounded once at every
internal node. The backward-error bound counts the multiplication and all
additions on a longest leaf-to-root path.
-/

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- The exact componentwise products, preserving the given reduction shape. -/
def exactProductTree (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => p.1 * p.2)

/-- The rounded componentwise products, preserving the given reduction shape. -/
def roundedProductTree (model : Model) (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => model.mul p.1 p.2)

/-- Round each componentwise product, then reduce with rounded addition
according to the original binary tree. -/
def roundedDotProduct (model : Model) (tree : Tree (ℝ × ℝ)) : ℝ :=
  roundedSum model (roundedProductTree model tree)

/-- The computed dot product is the exact sum of leafwise perturbations of
exact products. Each leaf changes by at most `gamma (tree.depth + 1) model.u`
times the absolute value of its exact product, with the original tree shape
preserved. The model accounts for multiplication and addition rounding, and
its specification incorporates the absence of overflow and underflow. -/
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
        obtain ⟨δ, hδ, hr⟩ := model.round_spec (p.1 * p.2)
        change |model.round (p.1 * p.2) - p.1 * p.2| ≤
          model.u * |p.1 * p.2|
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
  have hdepth : (tree.depth : ℝ) * model.u < 1 := by
    push_cast at hsmall
    nlinarith [model.u_nonneg]
  have hrounded : ((roundedProductTree model tree).depth : ℝ) * model.u < 1 := by
    simpa [roundedProductTree] using hdepth
  obtain ⟨perturbed, hadd, hsum⟩ :=
    roundedSum_exists_perturbation model (roundedProductTree model tree) hrounded
  have hadd' : IsPerturbation (gamma tree.depth model.u)
      (roundedProductTree model tree) perturbed := by
    simpa [roundedProductTree] using hadd
  refine ⟨perturbed, ?_, hsum⟩
  apply (hmul.trans hadd' (gamma_nonneg tree.depth model.u model.u_nonneg hdepth)).mono
  calc
    model.u + gamma tree.depth model.u * (1 + model.u) =
        gamma tree.depth model.u + model.u * (1 + gamma tree.depth model.u) := by ring
    _ ≤ gamma (tree.depth + 1) model.u :=
      gamma_step tree.depth model.u model.u_nonneg hsmall

end Research.BinaryTreeReduction
