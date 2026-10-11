import Research.Common.FloatingPoint.Model

/-! # Accumulated relative error -/

namespace Research.FloatingPoint

/-- Standard bound for `k` accumulated relative errors of size at most `u`. -/
noncomputable def gamma (k : ℕ) (u : ℝ) : ℝ :=
  (k : ℝ) * u / (1 - (k : ℝ) * u)

@[simp] theorem gamma_zero (u : ℝ) : gamma 0 u = 0 := by
  simp [gamma]

/-!
Next prove positivity and monotonicity of `gamma`, the representation
`∏ j, (1 + δ j) = 1 + θ`, and `|θ| ≤ gamma k u`.
-/

end Research.FloatingPoint
