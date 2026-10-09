import Mathlib

open scoped BigOperators

namespace Research

/-- The dot product of two real vectors indexed by `Fin n`. -/
def dotProduct {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i, x i * y i

/-- The real dot product is symmetric. -/
theorem dotProduct_comm {n : ℕ} (x y : Fin n → ℝ) :
    dotProduct x y = dotProduct y x := by
  sorry

end Research
