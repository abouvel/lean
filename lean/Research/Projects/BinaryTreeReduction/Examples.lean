import Research.Projects.BinaryTreeReduction.Algorithm
import Research.Projects.BinaryTreeReduction.Reduction

/-! # Small executable checks for binary-tree reduction -/

namespace Research.BinaryTreeReduction.Examples

open Research.FloatingPoint

/-- The four-input tree used in the explanatory derivation. -/
def fourLeafTree : Tree ℝ :=
  .node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 4) (.leaf 5))

example : fourLeafTree.depth = 2 := by
  norm_num [fourLeafTree, Tree.depth]

example : fourLeafTree.exactSum = 14 := by
  norm_num [fourLeafTree, Tree.exactSum]

/-- The five-input example follows the offset pairing in Algorithm 1. -/
def fiveInputs : List ℝ := [2, 3, 4, 5, 6]

example : exactLevelValues (reductionLevels fiveInputs) =
    [[2, 3, 4, 5, 6], [7, 9, 4], [11, 9], [20]] := by
  have hclog : Nat.clog 2 5 = 3 := by native_decide
  norm_num [fiveInputs, reductionLevels, hclog, reductionLevelsFromForest,
    reductionRound, combineHalves, exactLevelValues, Tree.exactSum]

/-- The unmatched third tree is copied to the next level as the same leaf;
no addition node is created around it. -/
example :
    reductionRound ([.leaf 2, .leaf 3, .leaf 4, .leaf 5, .leaf 6] : List (Tree ℝ)) =
      [.node (.leaf 2) (.leaf 5), .node (.leaf 3) (.leaf 6), .leaf 4] := by
  norm_num [reductionRound, combineHalves]

/-- The exact tree produced by all three rounds of the five-input example. -/
def fiveInputAlgorithmTree : Tree ℝ :=
  .node
    (.node (.node (.leaf 2) (.leaf 5)) (.leaf 4))
    (.node (.leaf 3) (.leaf 6))

example : reductionTree fiveInputs = some fiveInputAlgorithmTree := by
  have hclog : Nat.clog 2 5 = 3 := by native_decide
  norm_num [fiveInputs, fiveInputAlgorithmTree, reductionTree, finalForest,
    runRounds, reductionRound, combineHalves, hclog]

example : fiveInputAlgorithmTree.exactSum = 20 := by
  norm_num [fiveInputAlgorithmTree, Tree.exactSum]

example : fiveInputAlgorithmTree.depth = 3 := by
  norm_num [fiveInputAlgorithmTree, Tree.depth]

/-- The verified general theorem specializes directly to the four-input
example: every leaf changes by at most `gamma 2 u` relative to its magnitude.
-/
example (model : Model) (hsmall : (2 : ℝ) * model.u < 1) :
    ∃ perturbed : Tree ℝ,
      IsPerturbation (gamma 2 model.u) fourLeafTree perturbed ∧
      perturbed.exactSum = roundedSum model fourLeafTree := by
  apply roundedSum_exists_perturbation_of_depth_le model 2 fourLeafTree
  · norm_num [fourLeafTree, Tree.depth]
  · exact hsmall

end Research.BinaryTreeReduction.Examples
