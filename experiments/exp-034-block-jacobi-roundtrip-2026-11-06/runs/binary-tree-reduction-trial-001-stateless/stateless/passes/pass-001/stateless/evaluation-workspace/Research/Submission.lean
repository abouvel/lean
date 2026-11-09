import Mathlib

/-!
Formalization of Bhola, `theorem:parallel_binary_tree_reduction`.

Indices are zero based. Coordinates have an arbitrary index type, so in particular
`ι = Fin d` gives the source's finite-dimensional vectors. The standard relative
rounding model is represented by an error `δ ℓ k c` at each genuine addition.
The no-overflow/no-underflow arithmetic assumption is used precisely through
this local model; no backward-error conclusion is assumed.

Statement revision record: initial statement, checked against /spec/source.txt
and the algorithm in /spec/paper.tex. No /spec/feedback.json was supplied.
The support directory contained no files to copy.
-/

namespace Research.BinaryTreeReduction

noncomputable section

/-- The natural ceiling of the base-two logarithm of the input count. -/
def depth (n : ℕ) : ℕ := Nat.clog 2 n

/-- `ceil(n / 2^ℓ)`, the number of available nodes at stage `ℓ`. -/
def stageSize (n ℓ : ℕ) : ℕ := (n + 2 ^ ℓ - 1) / 2 ^ ℓ

/-- The deterministic error constant, used under `k * u < 1`. -/
def gamma (k : ℕ) (u : ℝ) : ℝ := (k : ℝ) * u / (1 - (k : ℝ) * u)

/-- The actual stage evaluation. A genuine addition is rounded componentwise
as `(a + b) * (1 + δ ℓ k c)`; an unmatched node is copied exactly.
Unavailable nodes are assigned zero solely to make the function total. -/
def stage {ι : Type*} {n : ℕ} (x : Fin n → ι → ℝ)
    (δ : ℕ → ℕ → ι → ℝ) : ℕ → ℕ → ι → ℝ
  | 0, k, c => if hk : k < n then x ⟨k, hk⟩ c else 0
  | ℓ + 1, k, c =>
      if k < stageSize n (ℓ + 1) then
        if k + stageSize n (ℓ + 1) < stageSize n ℓ then
          (stage x δ ℓ k c + stage x δ ℓ (k + stageSize n (ℓ + 1)) c) *
            (1 + δ ℓ k c)
        else stage x δ ℓ k c
      else 0

/-- The computed result is the first node of the final stage, rather than an
independent vector satisfying a presumed expansion. -/
def computed {ι : Type*} {n : ℕ} (x : Fin n → ι → ℝ)
    (δ : ℕ → ℕ → ι → ℝ) : ι → ℝ :=
  stage x δ (depth n) 0

/-- Admissibility of local rounding errors. Only additions actually performed
before the final stage require a bound; copies have no rounding error. -/
def LocalRoundingModel {ι : Type*} (n : ℕ) (u : ℝ)
    (δ : ℕ → ℕ → ι → ℝ) : Prop :=
  ∀ ℓ, ℓ < depth n → ∀ k, k < stageSize n (ℓ + 1) →
    k + stageSize n (ℓ + 1) < stageSize n ℓ → ∀ c, |δ ℓ k c| ≤ u

/-- Contributions of individual original leaves, propagated by the same
schedule and rounding factors as the computed stages. This construction does
not assume that a root coefficient is near one. -/
def coefficient {ι : Type*} {n : ℕ} (δ : ℕ → ℕ → ι → ℝ) :
    ℕ → ℕ → Fin n → ι → ℝ
  | 0, k, i, _ => if k = i.val then 1 else 0
  | ℓ + 1, k, i, c =>
      if k < stageSize n (ℓ + 1) then
        if k + stageSize n (ℓ + 1) < stageSize n ℓ then
          (coefficient δ ℓ k i c +
            coefficient δ ℓ (k + stageSize n (ℓ + 1)) i c) * (1 + δ ℓ k c)
        else coefficient δ ℓ k i c
      else 0

/-- A concrete perturbation of each input coordinate, with no division by
that coordinate (and hence also valid for zero inputs). -/
def backwardPerturbation {ι : Type*} {n : ℕ} (x : Fin n → ι → ℝ)
    (δ : ℕ → ℕ → ι → ℝ) : Fin n → ι → ℝ :=
  fun i c => x i c * (coefficient δ (depth n) 0 i c - 1)

lemma stageSize_le_iff (n l k : ℕ) : stageSize n l ≤ k ↔ n ≤ k * 2 ^ l := by
  have hp : 0 < 2 ^ l := pow_pos (by decide) _
  unfold stageSize
  rw [Nat.div_le_iff_le_mul hp]
  omega

lemma stageSize_zero (n : ℕ) : stageSize n 0 = n := by
  simp [stageSize]

lemma stageSize_bounds (n l : ℕ) :
    stageSize n (l + 1) ≤ stageSize n l ∧
    stageSize n l ≤ 2 * stageSize n (l + 1) := by
  have ha := (stageSize_le_iff n l (stageSize n l)).mp le_rfl
  have hb := (stageSize_le_iff n (l+1) (stageSize n (l+1))).mp le_rfl
  rw [pow_succ] at hb
  constructor
  · apply (stageSize_le_iff _ _ _).mpr
    rw [pow_succ]
    nlinarith
  · apply (stageSize_le_iff _ _ _).mpr
    nlinarith

lemma stageSize_final {n : ℕ} (hn : 0 < n) : stageSize n (depth n) = 1 := by
  have hle : stageSize n (depth n) ≤ 1 := by
    apply (stageSize_le_iff _ _ _).mpr
    simpa [depth] using Nat.le_pow_clog (by decide : 1 < 2) n
  have hpos : ¬ stageSize n (depth n) ≤ 0 := by
    rw [stageSize_le_iff]
    simp; omega
  omega

lemma gamma_nonneg {k : ℕ} {u : ℝ} (hu : 0 ≤ u) (hk : (k : ℝ) * u < 1) :
    0 ≤ gamma k u := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

lemma gamma_step {k : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (hk : ((k+1 : ℕ) : ℝ) * u < 1) :
    gamma k u + u + gamma k u * u ≤ gamma (k+1) u := by
  have hku : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hcast : ((k+1 : ℕ) : ℝ) = (k : ℝ) + 1 := by simp
  rw [hcast] at hk
  have h0 : 0 < 1 - (k : ℝ) * u := by nlinarith
  have h1 : 0 < 1 - ((k : ℝ) + 1) * u := by linarith
  unfold gamma
  rw [hcast]
  apply (le_div_iff₀ h1).mpr
  field_simp
  nlinarith [mul_nonneg (by positivity : 0 ≤ (k : ℝ) + 1) (sq_nonneg u)]

lemma rounded_bound {k : ℕ} {u p d : ℝ} (hu : 0 ≤ u)
    (hk : ((k+1 : ℕ) : ℝ) * u < 1)
    (hp : |p - 1| ≤ gamma k u) (hd : |d| ≤ u) :
    |p * (1+d) - 1| ≤ gamma (k+1) u := by
  have he : p * (1+d) - 1 = (p-1) + d + (p-1)*d := by ring
  rw [he]
  calc
    |(p-1) + d + (p-1)*d| ≤ |p-1| + |d| + |p-1| * |d| := by
      simpa [abs_mul] using (abs_add_le ((p-1)+d) ((p-1)*d)).trans
        (by simpa [abs_mul] using add_le_add (abs_add_le (p-1) d) (le_refl (|(p-1)*d|)))
    _ ≤ gamma k u + u + gamma k u * u := by
      have hg : 0 ≤ gamma k u := gamma_nonneg hu (by
        have : (k : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
        nlinarith)
      gcongr
    _ ≤ gamma (k+1) u := gamma_step hu hk

lemma coefficient_support_step {ι : Type*} {n l r : ℕ}
    (δ : ℕ → ℕ → ι → ℝ) (i : Fin n) (c : ι) (p : ℝ)
    (hr : r < stageSize n l)
    (hf : ∀ j, coefficient δ l j i c = if j = r then p else 0) :
    ∃ q, q < stageSize n (l+1) ∧
      (∀ j, coefficient δ (l+1) j i c =
        if j = q then
          (if q + stageSize n (l+1) < stageSize n l then
            p * (1 + δ l q c) else p) else 0) := by
  obtain ⟨hm, htwo⟩ := stageSize_bounds n l
  by_cases hrm : r < stageSize n (l+1)
  · refine ⟨r, hrm, ?_⟩
    intro j
    simp only [coefficient, hf]
    split_ifs <;> simp_all <;> omega
  · refine ⟨r - stageSize n (l+1), by omega, ?_⟩
    intro j
    have he : r - stageSize n (l+1) + stageSize n (l+1) = r := by omega
    simp only [coefficient, hf]
    split_ifs <;> simp_all <;> omega

lemma coefficient_path_bound {ι : Type*} {n : ℕ} (u : ℝ) (hu : 0 ≤ u)
    (δ : ℕ → ℕ → ι → ℝ) (hδ : LocalRoundingModel n u δ)
    (hsmall : (depth n : ℝ) * u < 1) (i : Fin n) (c : ι) :
    ∀ l, l ≤ depth n → ∃ r p, r < stageSize n l ∧
      (∀ j, coefficient δ l j i c = if j = r then p else 0) ∧
      |p-1| ≤ gamma l u := by
  intro l
  induction l with
  | zero =>
    intro _
    refine ⟨i.val, 1, ?_, ?_, ?_⟩
    · simpa [stageSize_zero] using i.isLt
    · intro j; rfl
    · simp [gamma]
  | succ l ih =>
    intro hl
    obtain ⟨r, p, hr, hf, hp⟩ := ih (by omega)
    obtain ⟨q, hq, hform⟩ := coefficient_support_step δ i c p hr hf
    have hs : ((l+1 : ℕ) : ℝ) * u < 1 := by
      have : ((l+1 : ℕ) : ℝ) ≤ (depth n : ℝ) := by exact_mod_cast hl
      nlinarith
    refine ⟨q, if q + stageSize n (l+1) < stageSize n l then
      p * (1 + δ l q c) else p, hq, hform, ?_⟩
    split_ifs with hadd
    · exact rounded_bound hu hs hp (hδ l (by omega) q hq hadd c)
    · have hg : gamma l u ≤ gamma (l+1) u := by
        have hg0 : 0 ≤ gamma l u := gamma_nonneg hu (by
          have : (l : ℝ) ≤ ((l+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ l
          nlinarith)
        have := gamma_step hu hs
        have := mul_nonneg hg0 hu
        linarith
      exact hp.trans hg

lemma stage_expansion {ι : Type*} {n : ℕ} (x : Fin n → ι → ℝ)
    (δ : ℕ → ℕ → ι → ℝ) (l k : ℕ) (c : ι) :
    stage x δ l k c = ∑ i : Fin n, x i c * coefficient δ l k i c := by
  induction l generalizing k with
  | zero =>
    simp only [stage, coefficient]
    by_cases hk : k < n
    · rw [dif_pos hk]
      have he (i : Fin n) : k = i.val ↔ i = ⟨k, hk⟩ := by
        simp [Fin.ext_iff, eq_comm]
      simp [he]
    · rw [dif_neg hk]
      symm
      apply Finset.sum_eq_zero
      intro i _
      have : k ≠ i.val := by have := i.isLt; omega
      simp [this]
  | succ l ih =>
    simp only [stage, coefficient]
    split_ifs with hk hadd
    · rw [ih, ih, ← Finset.sum_add_distrib, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · exact ih k
    · simp

/-- The canonical perturbations reconstruct the computed output and satisfy
exactly the componentwise bound in the selected theorem. The only smallness
assumption is `depth n * u < 1`; `n` need not be a power of two. -/
theorem canonical_backward_error {ι : Type*} {n : ℕ}
    (hn : 0 < n) (x : Fin n → ι → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (δ : ℕ → ℕ → ι → ℝ) (hδ : LocalRoundingModel n u δ)
    (hsmall : (depth n : ℝ) * u < 1) :
    computed x δ = ∑ i : Fin n, (x i + backwardPerturbation x δ i) ∧
      ∀ (i : Fin n) (c : ι),
        |backwardPerturbation x δ i c| ≤ gamma (depth n) u * |x i c| := by
  constructor
  · funext c
    simp only [Finset.sum_apply, Pi.add_apply]
    change stage x δ (depth n) 0 c = _
    rw [stage_expansion]
    apply Finset.sum_congr rfl
    intro i _
    simp only [backwardPerturbation]
    ring
  · intro i c
    obtain ⟨r, p, hr, hf, hp⟩ := coefficient_path_bound u hu δ hδ hsmall i c
      (depth n) le_rfl
    rw [stageSize_final hn] at hr
    have hr0 : r = 0 := by omega
    have he : coefficient δ (depth n) 0 i c = p := by simp [hf, hr0]
    simp only [backwardPerturbation, abs_mul, he]
    calc
      |x i c| * |p-1| ≤ |x i c| * gamma (depth n) u :=
        mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ = gamma (depth n) u * |x i c| := mul_comm _ _

/-- Full selected result: the actual binary-tree output admits a backward
error representation for every original input, with the logarithmic gamma
constant and componentwise inequalities. -/
theorem parallel_binary_tree_reduction {ι : Type*} {n : ℕ}
    (hn : 0 < n) (x : Fin n → ι → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (δ : ℕ → ℕ → ι → ℝ) (hδ : LocalRoundingModel n u δ)
    (hsmall : (depth n : ℝ) * u < 1) :
    ∃ Δx : Fin n → ι → ℝ,
      computed x δ = ∑ i : Fin n, (x i + Δx i) ∧
        ∀ (i : Fin n) (c : ι), |Δx i c| ≤ gamma (depth n) u * |x i c| := by
  exact ⟨backwardPerturbation x δ, canonical_backward_error hn x u hu δ hδ hsmall⟩

end

end Research.BinaryTreeReduction
