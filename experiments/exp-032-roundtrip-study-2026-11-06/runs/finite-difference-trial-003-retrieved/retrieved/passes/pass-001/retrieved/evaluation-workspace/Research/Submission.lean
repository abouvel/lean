import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Research

/-- The forward-difference approximation to the derivative of `f` at `x`
with step `h`. -/
noncomputable def forwardDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (f (x + h) - f x) / h

/-- A local variation bound on the interior derivative controls the error
of the forward difference. The value `D x` is a reference value; neither
endpoint is required to have a derivative. -/
theorem forwardDifference_error_bound
    (f D : ℝ → ℝ) (x h L : ℝ)
    (hh : 0 < h)
    (hL : 0 ≤ L)
    (hcontinuous : ContinuousOn f (Set.Icc x (x + h)))
    (hderivative : ∀ t ∈ Set.Ioo x (x + h), HasDerivAt f (D t) t)
    (hvariation : ∀ t ∈ Set.Ioo x (x + h),
      |D t - D x| ≤ L * |t - x|) :
    |forwardDifference f x h - D x| ≤ L * h := by
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope f D (by linarith : x < x + h)
      hcontinuous hderivative
  have hstep : x + h - x = h := by ring
  have hvalue : D c = forwardDifference f x h := by
    simpa [forwardDifference, hstep] using hslope
  have hnonneg : 0 ≤ c - x := by linarith [hc.1]
  have hdistance : c - x ≤ h := by linarith [hc.2]
  calc
    |forwardDifference f x h - D x| = |D c - D x| := by rw [hvalue]
    _ ≤ L * |c - x| := hvariation c hc
    _ ≤ L * h := by
      rw [abs_of_nonneg hnonneg]
      exact mul_le_mul_of_nonneg_left hdistance hL

end Research
