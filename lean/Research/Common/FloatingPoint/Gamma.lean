import Research.Common.FloatingPoint.Model

/-! # Accumulated relative error -/

namespace Research.FloatingPoint

/-- Standard bound for `k` accumulated relative errors of size at most `u`. -/
noncomputable def gamma (k : ℕ) (u : ℝ) : ℝ :=
  (k : ℝ) * u / (1 - (k : ℝ) * u)

@[simp] theorem gamma_zero (u : ℝ) : gamma 0 u = 0 := by
  simp [gamma]

/-- The product of the relative-error factors in a list. -/
def errorProduct (errors : List ℝ) : ℝ :=
  (errors.map fun δ => 1 + δ).prod

@[simp] theorem errorProduct_nil : errorProduct [] = 1 := by
  simp [errorProduct]

@[simp] theorem errorProduct_cons (δ : ℝ) (errors : List ℝ) :
    errorProduct (δ :: errors) = (1 + δ) * errorProduct errors := by
  simp [errorProduct]

/-- `gamma` is nonnegative whenever its denominator is positive. -/
theorem gamma_nonneg (k : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hsmall : (k : ℝ) * u < 1) :
    0 ≤ gamma k u := by
  unfold gamma
  exact div_nonneg (mul_nonneg (by positivity) hu) (le_of_lt (sub_pos.mpr hsmall))

/-- The algebraic step used when one more rounding-error factor is added. -/
theorem gamma_step (k : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hsmall : ((k + 1 : ℕ) : ℝ) * u < 1) :
    gamma k u + u * (1 + gamma k u) ≤ gamma (k + 1) u := by
  have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
  have hk_small : (k : ℝ) * u < 1 := by
    norm_num at hsmall ⊢
    nlinarith
  have hk_denom : 0 < 1 - (k : ℝ) * u := sub_pos.mpr hk_small
  have hsucc_denom : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := sub_pos.mpr hsmall
  rw [gamma, gamma]
  norm_num at hsmall ⊢
  have hleft :
      (k : ℝ) * u / (1 - (k : ℝ) * u) +
          u * (1 + (k : ℝ) * u / (1 - (k : ℝ) * u)) =
        ((k : ℝ) + 1) * u / (1 - (k : ℝ) * u) := by
    field_simp [ne_of_gt hk_denom]
    ring
  rw [hleft]
  exact div_le_div_of_nonneg_left
    (mul_nonneg (by positivity) hu)
    (by norm_num at hsucc_denom ⊢; exact hsucc_denom)
    (by nlinarith)

/-- A product of `k` relative-error factors differs from one by at most
`gamma k u`, provided each individual error is at most `u` and `k*u < 1`.
-/
theorem errorProduct_sub_one_abs_le_gamma (errors : List ℝ) (u : ℝ)
    (hu : 0 ≤ u)
    (hsmall : (errors.length : ℝ) * u < 1)
    (herrors : ∀ δ ∈ errors, |δ| ≤ u) :
    |errorProduct errors - 1| ≤ gamma errors.length u := by
  induction errors with
  | nil => simp
  | cons δ errors ih =>
      have hδ : |δ| ≤ u := herrors δ (by simp)
      have htail : ∀ ε ∈ errors, |ε| ≤ u := by
        intro ε hε
        exact herrors ε (by simp [hε])
      have htail_small : (errors.length : ℝ) * u < 1 := by
        norm_num at hsmall ⊢
        nlinarith
      have ih_bound := ih htail_small htail
      have hgamma_nonneg : 0 ≤ gamma errors.length u :=
        gamma_nonneg errors.length u hu htail_small
      have hproduct_abs : |errorProduct errors| ≤ 1 + gamma errors.length u := by
        calc
          |errorProduct errors| = |(errorProduct errors - 1) + 1| := by ring_nf
          _ ≤ |errorProduct errors - 1| + |(1 : ℝ)| := abs_add_le _ _
          _ ≤ gamma errors.length u + 1 := by norm_num; linarith
          _ = 1 + gamma errors.length u := by ring
      calc
        |errorProduct (δ :: errors) - 1|
            = |(errorProduct errors - 1) + δ * errorProduct errors| := by
                rw [errorProduct_cons]
                congr 1
                ring
        _ ≤ |errorProduct errors - 1| + |δ * errorProduct errors| := abs_add_le _ _
        _ = |errorProduct errors - 1| + |δ| * |errorProduct errors| := by
              rw [abs_mul]
        _ ≤ gamma errors.length u + u * (1 + gamma errors.length u) := by
              gcongr
        _ ≤ gamma (errors.length + 1) u := gamma_step errors.length u hu (by
              norm_num at hsmall ⊢
              exact hsmall)
        _ = gamma (δ :: errors).length u := by simp

end Research.FloatingPoint
