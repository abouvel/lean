import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Research

/-- The forward-difference approximation to the derivative of `f` at `x`
with step `h`. -/
noncomputable def forwardDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (f (x + h) - f x) / h

/-- A local bound on the variation of the prescribed interior derivative
controls the forward-difference error. The value `D x` is a reference value;
no derivative at either endpoint is assumed. -/
theorem forwardDifference_error_bound
    (f D : ℝ → ℝ) (x h L : ℝ)
    (h_pos : 0 < h)
    (L_nonneg : 0 ≤ L)
    (f_continuous : ContinuousOn f (Set.Icc x (x + h)))
    (f_derivative : ∀ t ∈ Set.Ioo x (x + h), HasDerivAt f (D t) t)
    (derivative_variation :
      ∀ t ∈ Set.Ioo x (x + h), |D t - D x| ≤ L * |t - x|) :
    |forwardDifference f x h - D x| ≤ L * h := by
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope f D (by linarith : x < x + h)
      f_continuous f_derivative
  have hquotient : D c = forwardDifference f x h := by
    simpa [forwardDifference] using hslope
  have hdistance : |c - x| ≤ h := by
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hc.1))]
    linarith [hc.2]
  rw [← hquotient]
  exact (derivative_variation c hc).trans (mul_le_mul_of_nonneg_left hdistance L_nonneg)

end Research
