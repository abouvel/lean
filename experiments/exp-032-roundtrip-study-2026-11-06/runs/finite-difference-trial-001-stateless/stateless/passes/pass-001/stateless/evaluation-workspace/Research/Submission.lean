import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Research

/-- The forward-difference approximation with step `h`. -/
noncomputable def forwardDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (f (x + h) - f x) / h

/-- A local derivative variation bound controls the forward-difference error.
The value `D x` is a reference value: no derivative at either endpoint is assumed.
-/
theorem forwardDifference_error_bound
    (f D : ℝ → ℝ) (x h L : ℝ)
    (hh : 0 < h)
    (hL : 0 ≤ L)
    (hcont : ContinuousOn f (Set.Icc x (x + h)))
    (hderiv : ∀ t ∈ Set.Ioo x (x + h), HasDerivAt f (D t) t)
    (hvariation : ∀ t ∈ Set.Ioo x (x + h), |D t - D x| ≤ L * |t - x|) :
    |forwardDifference f x h - D x| ≤ L * h := by
  have hxh : x < x + h := by linarith
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope f D hxh hcont hderiv
  have heq : D c = forwardDifference f x h := by
    simpa [forwardDifference] using hslope
  have hdist : |c - x| ≤ h := by
    rw [abs_of_nonneg (by linarith [hc.1] : 0 ≤ c - x)]
    linarith [hc.2]
  calc
    |forwardDifference f x h - D x| = |D c - D x| := by rw [heq]
    _ ≤ L * |c - x| := hvariation c hc
    _ ≤ L * h := mul_le_mul_of_nonneg_left hdist hL

end Research
