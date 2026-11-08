import Mathlib

namespace Research

/-- The forward-difference approximation with step `h`. -/
noncomputable def forwardDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (f (x + h) - f x) / h

/-- A local bound on variation of the interior derivative controls the error
of the forward difference. The value `D x` is a reference value; no endpoint
derivative is assumed. -/
theorem forwardDifference_error_bound
    (f D : ℝ → ℝ) (x h L : ℝ)
    (h_pos : 0 < h)
    (L_nonneg : 0 ≤ L)
    (hf_cont : ContinuousOn f (Set.Icc x (x + h)))
    (hf_deriv : ∀ t ∈ Set.Ioo x (x + h), HasDerivAt f (D t) t)
    (hD_variation : ∀ t ∈ Set.Ioo x (x + h),
      |D t - D x| ≤ L * |t - x|) :
    |forwardDifference f x h - D x| ≤ L * h := by
  have hx : x < x + h := by linarith
  obtain ⟨c, hc, hsec⟩ :=
    exists_hasDerivAt_eq_slope f D hx hf_cont hf_deriv
  have hforward : forwardDifference f x h = D c := by
    simpa [forwardDifference] using hsec.symm
  rw [hforward]
  have hdist : |c - x| ≤ h := by
    rw [abs_of_nonneg (by linarith [hc.1])]
    linarith [hc.2]
  exact (hD_variation c hc).trans (mul_le_mul_of_nonneg_left hdist L_nonneg)

end Research
