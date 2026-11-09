import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Research

/-- The forward-difference approximation with step `h`. -/
noncomputable def forwardDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (f (x + h) - f x) / h

/-- A local derivative variation bound controls the forward-difference error.
Only interior derivatives are required; `D x` is a reference value, with no
assumption that it is a derivative at the endpoint `x`. -/
theorem forwardDifference_error_bound
    (f D : ℝ → ℝ) (x h L : ℝ)
    (hh : 0 < h)
    (hL : 0 ≤ L)
    (hcont : ContinuousOn f (Set.Icc x (x + h)))
    (hderiv : ∀ t ∈ Set.Ioo x (x + h), HasDerivAt f (D t) t)
    (hvariation : ∀ t ∈ Set.Ioo x (x + h),
      |D t - D x| ≤ L * |t - x|) :
    |forwardDifference f x h - D x| ≤ L * h := by
  have hxh : x < x + h := lt_add_of_pos_right x hh
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope f D hxh hcont hderiv
  have hslope' : D c = forwardDifference f x h := by
    simpa [forwardDifference] using hslope
  have hdist : |c - x| ≤ h := by
    rw [abs_of_nonneg (sub_nonneg.mpr hc.1.le)]
    linarith [hc.2]
  rw [← hslope']
  exact (hvariation c hc).trans (mul_le_mul_of_nonneg_left hdist hL)

end Research
