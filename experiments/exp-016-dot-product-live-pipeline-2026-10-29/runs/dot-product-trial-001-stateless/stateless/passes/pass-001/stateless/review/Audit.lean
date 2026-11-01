import Research.Submission
open Research.FloatingPoint Research.BinaryTreeReduction
#check Research.BinaryTreeReduction.roundedDotProduct_exists_perturbation
#print axioms Research.BinaryTreeReduction.roundedDotProduct_exists_perturbation
example (model : Model) (tree : Research.BinaryTreeReduction.Tree (ℝ × ℝ))
    (hsmall : ((tree.depth + 1 : ℕ) : ℝ) * model.u < 1) :
    ∃ perturbed : Research.BinaryTreeReduction.Tree ℝ,
      IsPerturbation (gamma (tree.depth + 1) model.u)
        (tree.map (fun p => p.1 * p.2)) perturbed ∧
      perturbed.exactSum =
        roundedSum model (tree.map (fun p => model.round (p.1 * p.2))) := by
  exact roundedDotProduct_exists_perturbation model tree hsmall
