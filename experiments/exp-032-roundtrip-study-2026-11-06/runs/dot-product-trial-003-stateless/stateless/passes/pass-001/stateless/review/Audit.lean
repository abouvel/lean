import Research.Submission
open Research.FloatingPoint Research.BinaryTreeReduction
#print axioms roundedDotProduct_exists_perturbation
#check @roundedDotProduct_exists_perturbation
example (model : Model) (tree : Research.BinaryTreeReduction.Tree (ℝ × ℝ))
    (h : ((tree.depth + 1 : ℕ) : ℝ) * model.u < 1) :
    ∃ p : Research.BinaryTreeReduction.Tree ℝ,
      IsPerturbation (gamma (tree.depth + 1) model.u)
        (tree.map (fun xy => xy.1 * xy.2)) p ∧
      p.exactSum = roundedSum model (tree.map (fun xy => model.round (xy.1 * xy.2))) := by
  exact roundedDotProduct_exists_perturbation model tree h
