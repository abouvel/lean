import Research.Submission
open Research.FloatingPoint Research.BinaryTreeReduction
#check @dotProductBackwardError
#print axioms Research.BinaryTreeReduction.dotProductBackwardError
example (model : Model) (tree : Research.BinaryTreeReduction.Tree (ℝ × ℝ))
    (hsmall : ((tree.depth + 1 : ℕ) : ℝ) * model.u < 1) :
    ∃ perturbed : Research.BinaryTreeReduction.Tree ℝ,
      IsPerturbation (gamma (tree.depth + 1) model.u)
        (tree.map (fun pair => pair.1 * pair.2)) perturbed ∧
      perturbed.exactSum = roundedSum model
        (tree.map (fun pair => model.round (pair.1 * pair.2))) := by
  exact dotProductBackwardError model tree hsmall
