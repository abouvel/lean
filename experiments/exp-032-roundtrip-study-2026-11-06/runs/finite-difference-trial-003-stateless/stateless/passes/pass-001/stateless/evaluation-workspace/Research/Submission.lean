import Mathlib

namespace Research

/-- The forward-difference approximation to a real function at `x` with step `h`. -/
noncomputable def forwardDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (f (x + h) - f x) / h

/-- A local bound on the variation of the interior derivatives controls the
forward-difference error. The value `D x` is only a reference value; neither
endpoint is required to be a point of differentiability.

Source: `/spec/source.txt`. Initial statement; no feedback file was supplied
and no statement revision was made. -/
theorem forwardDifference_error_bound
    (f D : ℝ → ℝ) (x h L : ℝ)
    (hh : 0 < h)
    (hL : 0 ≤ L)
    (hcont : ContinuousOn f (Set.Icc x (x + h)))
    (hderiv : ∀ t ∈ Set.Ioo x (x + h), HasDerivAt f (D t) t)
    (hvariation : ∀ t ∈ Set.Ioo x (x + h), |D t - D x| ≤ L * |t - x|) :
    |forwardDifference f x h - D x| ≤ L * h := by
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope f D (show x < x + h by linarith) hcont hderiv
  have heq : D c = forwardDifference f x h := by
    simpa [forwardDifference] using hslope
  rw [← heq]
  calc
    |D c - D x| ≤ L * |c - x| := hvariation c hc
    _ ≤ L * h := by
      apply mul_le_mul_of_nonneg_left _ hL
      rw [abs_of_nonneg (sub_nonneg.mpr hc.1.le)]
      linarith [hc.2]

end Research
