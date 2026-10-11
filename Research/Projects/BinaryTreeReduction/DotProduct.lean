import Research.Projects.BinaryTreeReduction.Reduction

/-! # Floating-point dot product -/

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- One rounded componentwise product before tree reduction. -/
def roundedProductTerm (model : Model) (x y : ℝ) : ℝ :=
  model.mul x y

/-!
After the reduction theorem, bound each multiplication error, reduce the
rounded products through the tree, and combine one multiplication error with
at most `⌈log₂ n⌉` addition errors per term.

This is separate from the existing exact-real commutativity pilot.
-/

end Research.BinaryTreeReduction
