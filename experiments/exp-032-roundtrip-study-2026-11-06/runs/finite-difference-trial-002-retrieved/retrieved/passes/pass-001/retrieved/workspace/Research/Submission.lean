import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Formalization of /spec/source.txt.

There are no supplied supporting sources and no /spec/feedback.json.
Statement revisions: none. The original endpoint scope is preserved:
`D x` is a reference value, and no endpoint derivative is assumed.
-/

namespace Research

/-- The forward-difference approximation to a real function at `x` with step `h`. -/
noncomputable def forwardDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (f (x + h) - f x) / h

/-- An interior derivative variation bound controls the forward-difference error.
The derivative is required only in the open interval; `D x` is the reference
value appearing in the variation hypothesis. -/
theorem forwardDifference_error_bound
    (f D : ℝ → ℝ) (x h L : ℝ)
    (h_pos : 0 < h)
    (L_nonneg : 0 ≤ L)
    (hf_cont : ContinuousOn f (Set.Icc x (x + h)))
    (hf_deriv : ∀ t ∈ Set.Ioo x (x + h), HasDerivAt f (D t) t)
    (hD_variation : ∀ t ∈ Set.Ioo x (x + h),
      |D t - D x| ≤ L * |t - x|) :
    |forwardDifference f x h - D x| ≤ L * h := by
  have h_interval : x < x + h := by linarith
  obtain ⟨c, hc, h_slope⟩ :=
    exists_hasDerivAt_eq_slope f D h_interval hf_cont hf_deriv
  have h_forward : D c = forwardDifference f x h := by
    simpa [forwardDifference] using h_slope
  have h_distance_nonneg : 0 ≤ c - x := by linarith [hc.1]
  have h_distance_le : c - x ≤ h := by linarith [hc.2]
  rw [← h_forward]
  calc
    |D c - D x| ≤ L * |c - x| := hD_variation c hc
    _ = L * (c - x) := by rw [abs_of_nonneg h_distance_nonneg]
    _ ≤ L * h := mul_le_mul_of_nonneg_left h_distance_le L_nonneg

end Research
