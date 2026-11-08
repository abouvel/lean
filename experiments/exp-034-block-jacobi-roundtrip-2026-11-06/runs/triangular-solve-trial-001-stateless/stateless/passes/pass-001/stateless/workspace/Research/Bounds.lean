import Mathlib

namespace TriangularSolveBounds

noncomputable def g (n : ℕ) (u : ℝ) := (n : ℝ) * u / (1 - (n : ℝ) * u)

lemma g_nonneg {n : ℕ} {u : ℝ} (hu : 0 ≤ u) (hn : (n : ℝ)*u < 1) :
    0 ≤ g n u := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

lemma g_mono {m n : ℕ} {u : ℝ} (hu : 0 ≤ u) (hmn : m ≤ n)
    (hn : (n : ℝ)*u < 1) : g m u ≤ g n u := by
  have hmul : (m : ℝ)*u ≤ (n : ℝ)*u := mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hu
  unfold g
  apply (div_le_div_iff₀ (by linarith : 0 < 1-(m:ℝ)*u) (by linarith : 0 < 1-(n:ℝ)*u)).2
  nlinarith

lemma g_step {m : ℕ} {u : ℝ} (hu : 0 ≤ u) (hn : ((m+1 : ℕ):ℝ)*u < 1) :
    (1+u)*g m u+u ≤ g (m+1) u := by
  have hm : (m:ℝ)*u < 1 := by push_cast at hn; nlinarith [Nat.cast_nonneg (α := ℝ) m]
  unfold g
  apply (le_div_iff₀ (by linarith : 0 < 1-((m+1:ℕ):ℝ)*u)).2
  have he : (m:ℝ)*u / (1-(m:ℝ)*u) * (1-(m:ℝ)*u) = (m:ℝ)*u := div_mul_cancel₀ _ (by linarith)
  push_cast at *
  nlinarith [sq_nonneg u, mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sq_nonneg u)]

lemma two_round {m : ℕ} {u : ℝ} (hu : 0 ≤ u) (hm : 1 ≤ m)
    (hn : ((m+1:ℕ):ℝ)*u < 1) : (2+u)*u ≤ g (m+1) u := by
  have h2 : (2:ℝ)*u < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast (show 2 ≤ m+1 by omega)) hu) hn
  have h : (2+u)*u ≤ g 2 u := by
    unfold g
    norm_num
    apply (le_div_iff₀ (by linarith : 0 < 1-2*u)).2
    nlinarith [mul_nonneg hu (sq_nonneg u)]
  exact h.trans (g_mono hu (by omega) hn)

lemma inverse_error {u δ : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) (hd : |δ| ≤ u) :
    |(1+δ)⁻¹-1| ≤ g 1 u := by
  have hδ := abs_le.mp hd
  have hp : 0 < 1+δ := by linarith
  have hid : (1+δ)⁻¹-1 = -δ/(1+δ) := by field_simp; ring
  rw [hid, abs_div, abs_neg, abs_of_pos hp]
  unfold g
  norm_num
  apply (div_le_div_iff₀ hp (by linarith : 0 < 1-u)).2
  have hab := abs_nonneg δ
  have hδabs : -δ ≤ |δ| := neg_le_abs δ
  nlinarith

lemma inverse_two_error {u δ ε : ℝ} (hu : 0 ≤ u) (h2 : 2*u < 1)
    (hd : |δ| ≤ u) (he : |ε| ≤ u) :
    |((1+δ)*(1+ε))⁻¹-1| ≤ g 2 u := by
  have hd' := abs_le.mp hd
  have he' := abs_le.mp he
  have hp : 0 < 1+δ := by linarith
  have hq : 0 < 1+ε := by linarith
  have hlo : (1-u)^2 ≤ (1+δ)*(1+ε) := by nlinarith [mul_nonneg (by linarith : 0 ≤ δ+u) (by linarith : 0 ≤ ε+u)]
  have hhi : (1+δ)*(1+ε) ≤ (1+u)^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ u-δ) (by linarith : 0 ≤ u-ε)]
  have hprod : 0 < (1+δ)*(1+ε) := mul_pos hp hq
  have hid : ((1+δ)*(1+ε))⁻¹-1 = (1-(1+δ)*(1+ε))/((1+δ)*(1+ε)) := by field_simp
  rw [hid, abs_div, abs_of_pos hprod]
  unfold g
  norm_num
  apply (div_le_div_iff₀ hprod (by linarith : 0 < 1-2*u)).2
  have ha : |1-(1+δ)*(1+ε)| ≤ 2*u / (1-2*u) * ((1+δ)*(1+ε)) := by
    apply abs_le.mpr
    constructor
    · apply (mul_le_mul_iff_left₀ (by linarith : 0 < 1-2*u)).mp
      have hbound : ((1+δ)*(1+ε)) * (1-4*u) ≤ 1-2*u := by
        by_cases h4 : 4*u ≤ 1
        · have h := mul_le_mul_of_nonneg_right hhi (by linarith : 0 ≤ 1-4*u)
          nlinarith [sq_nonneg u, mul_nonneg hu (sq_nonneg u)]
        · have h := mul_nonpos_of_nonneg_of_nonpos hprod.le (by linarith : 1-4*u ≤ 0)
          linarith
      have heq : 2*u/(1-2*u)*(1-2*u) = 2*u := div_mul_cancel₀ _ (by linarith)
      have heq' := congrArg (fun t : ℝ => t*((1+δ)*(1+ε))) heq
      nlinarith only [hbound, heq', h2]
    · apply (mul_le_mul_iff_left₀ (by linarith : 0 < 1-2*u)).mp
      have heq : 2*u/(1-2*u)*(1-2*u) = 2*u := div_mul_cancel₀ _ (by linarith)
      have hl : 1-2*u ≤ (1+δ)*(1+ε) := by nlinarith [sq_nonneg u]
      have heq' := congrArg (fun t : ℝ => t*((1+δ)*(1+ε))) heq
      nlinarith only [hl, heq', h2]
  have hh := mul_le_mul_of_nonneg_right ha (by linarith : 0 ≤ 1-2*u)
  have heq : 2*u/(1-2*u)*(1-2*u) = 2*u := div_mul_cancel₀ _ (by linarith)
  have heq' := congrArg (fun t : ℝ => t*((1+δ)*(1+ε))) heq
  nlinarith only [hh, heq']

end TriangularSolveBounds
