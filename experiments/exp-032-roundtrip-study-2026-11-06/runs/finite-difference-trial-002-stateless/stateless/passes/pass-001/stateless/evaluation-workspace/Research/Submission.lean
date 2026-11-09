import Mathlib

namespace Research

/-- The forward-difference approximation with step `h`. -/
noncomputable def forwardDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (f (x + h) - f x) / h

/-- A local variation estimate on interior derivatives bounds the error of
the forward difference relative to the reference value `D x`.
Neither endpoint is required to be a point of differentiability. -/
theorem forwardDifference_error_bound
    (f D : ℝ → ℝ) (x h L : ℝ)
    (hh : 0 < h)
    (hL : 0 ≤ L)
    (hcont : ContinuousOn f (Set.Icc x (x + h)))
    (hderiv : ∀ t ∈ Set.Ioo x (x + h), HasDerivAt f (D t) t)
    (hvariation : ∀ t ∈ Set.Ioo x (x + h),
      |D t - D x| ≤ L * |t - x|) :
    |forwardDifference f x h - D x| ≤ L * h := by
  have hxh : x < x + h := by linarith
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope f D hxh hcont hderiv
  have hdist : |c - x| ≤ h := by
    rw [abs_of_nonneg (by linarith [hc.1] : 0 ≤ c - x)]
    linarith [hc.2]
  have hslope' : D c = forwardDifference f x h := by
    simpa [forwardDifference] using hslope
  rw [← hslope']
  exact (hvariation c hc).trans (mul_le_mul_of_nonneg_left hdist hL)

end Research
