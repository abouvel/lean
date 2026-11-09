import Research.Projects.BinaryTreeReduction.Reduction

/-!
# Rounded dot products on binary reduction trees

Each leaf stores a pair of real inputs. Multiplication is rounded once at
each leaf, and addition is rounded once at each internal node. The final
backward-error statement measures perturbations of the exact products.

Statement revision record: no `/spec/feedback.json` was supplied. The statement
below implements `/spec/source.txt` without changes to its assumptions or bound.
-/

noncomputable section

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- The original tree shape with each input pair replaced by its exact product. -/
def exactProductTree (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => p.1 * p.2)

/-- Round each componentwise multiplication once, preserving the tree shape. -/
def roundedProductTree (model : Model) (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map (fun p => model.mul p.1 p.2)

/-- Evaluate the rounded products with a rounded addition at each internal node. -/
def roundedDotProduct (model : Model) (tree : Tree (ℝ × ℝ)) : ℝ :=
  roundedSum model (roundedProductTree model tree)

/-- Every rounded tree dot product is the exact sum of leafwise perturbations
of the exact products. One multiplication and at most `tree.depth` additions
contribute rounding error along each leaf-to-root path. The abstract model
supplies nonnegativity of `u` and the relative-error specification for rounding;
the only additional assumption is the displayed depth-plus-one smallness bound.
-/
theorem roundedDotProduct_exists_perturbation
    (model : Model) (tree : Tree (ℝ × ℝ))
    (hsmall : ((tree.depth + 1 : ℕ) : ℝ) * model.u < 1) :
    ∃ perturbed : Tree ℝ,
      IsPerturbation (gamma (tree.depth + 1) model.u)
        (exactProductTree tree) perturbed ∧
      perturbed.exactSum = roundedDotProduct model tree := by
  have hproducts : IsPerturbation model.u (exactProductTree tree)
      (roundedProductTree model tree) := by
    clear hsmall
    induction tree with
    | leaf p =>
        obtain ⟨δ, hδ, hround⟩ := model.round_spec (p.1 * p.2)
        apply IsPerturbation.leaf
        change |model.round (p.1 * p.2) - p.1 * p.2| ≤ model.u * |p.1 * p.2|
        rw [hround]
        calc
          |p.1 * p.2 * (1 + δ) - p.1 * p.2| = |δ| * |p.1 * p.2| := by
            rw [← abs_mul]
            congr 1
            ring
          _ ≤ model.u * |p.1 * p.2| :=
            mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
    | node left right ihLeft ihRight =>
        exact IsPerturbation.node ihLeft ihRight
  have hdepth_small : (tree.depth : ℝ) * model.u < 1 := by
    norm_num at hsmall ⊢
    nlinarith [model.u_nonneg]
  obtain ⟨perturbed, hperturbed, hsum⟩ :=
    roundedSum_exists_perturbation model (roundedProductTree model tree) (by
      simpa [roundedProductTree] using hdepth_small)
  have hperturbed' : IsPerturbation (gamma tree.depth model.u)
      (roundedProductTree model tree) perturbed := by
    simpa [roundedProductTree] using hperturbed
  refine ⟨perturbed, ?_, hsum⟩
  have hcomposed := hproducts.trans hperturbed'
    (gamma_nonneg tree.depth model.u model.u_nonneg hdepth_small)
  apply hcomposed.mono
  calc
    model.u + gamma tree.depth model.u * (1 + model.u) =
        gamma tree.depth model.u + model.u * (1 + gamma tree.depth model.u) := by ring
    _ ≤ gamma (tree.depth + 1) model.u :=
      gamma_step tree.depth model.u model.u_nonneg hsmall

end Research.BinaryTreeReduction
