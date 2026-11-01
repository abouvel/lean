import Research.Submission
#print Research.BinaryTreeReduction.dotProductBackwardError
#print axioms Research.BinaryTreeReduction.dotProductBackwardError
example (model : Research.FloatingPoint.Model)
    (tree : Research.BinaryTreeReduction.Tree (ℝ × ℝ))
    (hsmall : ((tree.depth + 1 : ℕ) : ℝ) * model.u < 1) :
    ∃ perturbed : Research.BinaryTreeReduction.Tree ℝ,
      Research.BinaryTreeReduction.IsPerturbation
        (Research.FloatingPoint.gamma (tree.depth + 1) model.u)
        (Research.BinaryTreeReduction.exactProductTree tree) perturbed ∧
      perturbed.exactSum = Research.BinaryTreeReduction.roundedDotProduct model tree :=
  Research.BinaryTreeReduction.dotProductBackwardError model tree hsmall
