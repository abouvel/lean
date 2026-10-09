import Mathlib

/-!
# Dot product experiment

This file is the first small test of the informal-proof-to-Lean pipeline.
The theorem statement is fixed before Aristotle is asked to prove it.
-/

open scoped BigOperators

namespace Research

/-- The dot product of two real vectors indexed by `Fin n`. -/
def dotProduct {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i, x i * y i

/-- The real dot product is symmetric. -/
theorem dotProduct_comm {n : ℕ} (x y : Fin n → ℝ) :
    dotProduct x y = dotProduct y x := by
  unfold dotProduct
  exact Finset.sum_congr rfl fun i _ => mul_comm (x i) (y i)

end Research
