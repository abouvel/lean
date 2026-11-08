import Mathlib

/-!
Statement of the real-arithmetic update-form block Jacobi theorem from
`/spec/source.txt` (theorem:block_jacobi_real). The definitions are executable
mathematical constructions; only the final theorem is left for the proof role.
-/

open scoped BigOperators Matrix
open Filter Topology
open scoped ENNReal NNReal

namespace Research.BlockJacobi

abbrev Vector (n : ℕ) := Fin n → ℝ
abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A coordinate partition specifies arbitrary, possibly unequal block sizes.
Unused block labels have no effect. -/
def IsBlockDecomposition {n : ℕ} {B : Type*} (block : Fin n → B)
    (A D N : RealMatrix n) : Prop :=
  A = D + N ∧
    (∀ i j, block i ≠ block j → D i j = 0) ∧
    (∀ i j, block i = block j → N i j = 0)

/-- The maximum absolute coordinate, with value zero in dimension zero. -/
noncomputable def vectorInfNorm {n : ℕ} (v : Vector n) : ℝ :=
  ↑(Finset.univ.sup fun i => ‖v i‖₊)

/-- The induced infinity norm: maximum absolute row sum, not maximum entry. -/
noncomputable def matrixInfNorm {n : ℕ} (M : RealMatrix n) : ℝ :=
  ↑(Finset.univ.sup fun i => ∑ j, ‖M i j‖₊)

def vectorAbs {n : ℕ} (v : Vector n) : Vector n := fun i => |v i|

def matrixAbs {n : ℕ} (M : RealMatrix n) : RealMatrix n := fun i j => |M i j|

/-- Complexification retains all complex eigenvalues of the real matrix. -/
noncomputable def complexification {n : ℕ} (M : RealMatrix n) : Matrix (Fin n) (Fin n) ℂ :=
  M.map (algebraMap ℝ ℂ)

/-- The usual complex spectral radius. It is finite for finite matrices; the
empty-dimensional spectrum has radius zero by the supremum convention. -/
noncomputable def rho {n : ℕ} (M : RealMatrix n) : ℝ :=
  (spectralRadius ℂ (complexification M)).toReal

noncomputable def iterationMatrix {n : ℕ} (D N : RealMatrix n) : RealMatrix n :=
  -(D⁻¹ * N)

/-- Correction computed from the residual at the current approximation. -/
noncomputable def correctionAt {n : ℕ} (A D : RealMatrix n)
    (b y : Vector n) : Vector n :=
  D⁻¹ *ᵥ (b - A *ᵥ y)

noncomputable def update {n : ℕ} (A D : RealMatrix n)
    (b y : Vector n) : Vector n :=
  y + correctionAt A D b y

/-- Exact update-form Jacobi iteration for an arbitrary initial guess. -/
noncomputable def iterate {n : ℕ} (A D : RealMatrix n)
    (b x₀ : Vector n) : ℕ → Vector n
  | 0 => x₀
  | k + 1 => update A D b (iterate A D b x₀ k)

/-- `correction ... k` denotes the paper's correction c^(k+1). -/
noncomputable def correction {n : ℕ} (A D : RealMatrix n)
    (b x₀ : Vector n) (k : ℕ) : Vector n :=
  correctionAt A D b (iterate A D b x₀ k)

noncomputable def error {n : ℕ} (A D : RealMatrix n)
    (b x x₀ : Vector n) (k : ℕ) : Vector n :=
  iterate A D b x₀ k - x

lemma update_sub {n : ℕ} (A D N : RealMatrix n) (b : Vector n)
    (hA : A = D + N) (hD : IsUnit D.det) (u v : Vector n) :
    update A D b u - update A D b v = iterationMatrix D N *ᵥ (u - v) := by
  have hi : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D hD
  unfold update correctionAt iterationMatrix
  rw [hA, Matrix.neg_mulVec, Matrix.mulVec_sub, Matrix.mulVec_sub,
    Matrix.add_mulVec, Matrix.add_mulVec]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hi,
    Matrix.one_mulVec]
  abel

lemma update_fixed {n : ℕ} (A D : RealMatrix n) (b x : Vector n)
    (hx : A *ᵥ x = b) : update A D b x = x := by
  simp [update, correctionAt, hx]

lemma error_step {n : ℕ} (A D N : RealMatrix n) (b x x₀ : Vector n)
    (hA : A = D + N) (hD : IsUnit D.det) (hx : A *ᵥ x = b) (k : ℕ) :
    error A D b x x₀ (k+1) = iterationMatrix D N *ᵥ error A D b x x₀ k := by
  simpa only [error, iterate, update_fixed A D b x hx] using
    update_sub A D N b hA hD (iterate A D b x₀ k) x

lemma error_power {n : ℕ} (A D N : RealMatrix n) (b x x₀ : Vector n)
    (hA : A = D + N) (hD : IsUnit D.det) (hx : A *ᵥ x = b) (k : ℕ) :
    error A D b x x₀ k = iterationMatrix D N ^ k *ᵥ (x₀ - x) := by
  induction k with
  | zero => simp [error, iterate]
  | succ k ih => rw [error_step A D N b x x₀ hA hD hx, ih, Matrix.mulVec_mulVec, pow_succ']

lemma abs_mulVec_le {n : ℕ} (M : RealMatrix n) (v : Vector n) (i : Fin n) :
    vectorAbs (M *ᵥ v) i ≤ (matrixAbs M *ᵥ vectorAbs v) i := by
  simp only [vectorAbs, matrixAbs, Matrix.mulVec, dotProduct]
  exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp [abs_mul])

lemma abs_power_le {n : ℕ} (M : RealMatrix n) (v : Vector n) (k : ℕ) :
    ∀ i, vectorAbs (M ^ k *ᵥ v) i ≤ (matrixAbs M ^ k *ᵥ vectorAbs v) i := by
  induction k with
  | zero => simp [vectorAbs]
  | succ k ih =>
    rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    intro i
    refine (abs_mulVec_le _ _ i).trans ?_
    change (∑ j, |M i j| * vectorAbs (M ^ k *ᵥ v) j) ≤
      ∑ j, |M i j| * (matrixAbs M ^ k *ᵥ vectorAbs v) j
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (abs_nonneg _)

open scoped Matrix.Norms.Operator in
lemma inf_mulVec_le {n : ℕ} (M : RealMatrix n) (v : Vector n) :
    vectorInfNorm (M *ᵥ v) ≤ matrixInfNorm M * vectorInfNorm v := by
  change ‖M *ᵥ v‖ ≤ _
  rw [show matrixInfNorm M = ‖M‖ from (Matrix.linfty_opNorm_def M).symm]
  exact Matrix.linfty_opNorm_mulVec M v

lemma inf_nonneg {n : ℕ} (M : RealMatrix n) : 0 ≤ matrixInfNorm M := NNReal.coe_nonneg _

lemma inf_power_le {n : ℕ} (M : RealMatrix n) (v : Vector n) (k : ℕ) :
    vectorInfNorm (M ^ k *ᵥ v) ≤ matrixInfNorm M ^ k * vectorInfNorm v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, pow_succ']
    exact (inf_mulVec_le _ _).trans ((mul_le_mul_of_nonneg_left ih (inf_nonneg M)).trans_eq (mul_assoc ..).symm)

lemma rho_neg {n : ℕ} (M : RealMatrix n) : rho (-M) = rho M := by
  have hc : complexification (-M) = -complexification M := by ext i j; simp [complexification]
  unfold rho
  rw [hc]
  congr 1
  simp only [spectralRadius, ← spectrum.neg_eq, Set.mem_neg]
  apply le_antisymm
  · refine iSup₂_le fun z hz => ?_
    simpa using (le_iSup₂_of_le (-z) hz (by simp))
  · refine iSup₂_le fun z hz => ?_
    simpa using (le_iSup₂_of_le (-z) (by simpa using hz) (by simp))

open scoped Matrix.Norms.Operator in
lemma complex_power_criterion {n : ℕ} [Nonempty (Fin n)] (M : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (fun k : ℕ => M ^ k) atTop (𝓝 0) ↔ spectralRadius ℂ M < 1 := by
  have hf : spectralRadius ℂ M ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top
    (spectrum.spectralRadius_le_nnnorm M)
  constructor
  · intro h
    obtain ⟨k, hk, hn⟩ :=
      ((h.norm.eventually (gt_mem_nhds (show ‖(0 : Matrix (Fin n) (Fin n) ℂ)‖ < 1 by simp))).and
        (eventually_gt_atTop 0)).exists
    have hp : spectralRadius ℂ M ^ k < 1 :=
      (spectrum.spectralRadius_pow_le' M k).trans_lt
        ((spectrum.spectralRadius_le_nnnorm (M ^ k)).trans_lt (by exact_mod_cast hk))
    by_contra hh
    exact (not_lt_of_ge (one_le_pow₀ (le_of_not_gt hh))) hp
  · intro h
    have hr : (spectralRadius ℂ M).toReal < 1 := by
      simpa using (ENNReal.toReal_lt_toReal hf ENNReal.one_ne_top).mpr h
    obtain ⟨r, hr₁, hr₂⟩ := exists_between hr
    have rpos : 0 ≤ r := ENNReal.toReal_nonneg.trans hr₁.le
    have ht : Tendsto (fun k : ℕ => ‖M ^ k‖ ^ (1 / k : ℝ)) atTop
        (𝓝 (spectralRadius ℂ M).toReal) := by
      have := (ENNReal.tendsto_toReal hf).comp
        (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius M)
      simpa only [Function.comp_def, ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using this
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun k => norm_nonneg (M ^ k)) _
      (tendsto_pow_atTop_nhds_zero_of_lt_one rpos hr₂)
    filter_upwards [ht.eventually (gt_mem_nhds hr₁), eventually_gt_atTop 0] with k hk hn
    have he : (‖M ^ k‖ ^ (1 / k : ℝ)) ^ k = ‖M ^ k‖ := by
      simpa only [one_div] using Real.rpow_inv_natCast_pow (norm_nonneg (M ^ k)) (Nat.ne_of_gt hn)
    rw [← he]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hk.le k

lemma complexification_pow {n : ℕ} (M : RealMatrix n) (k : ℕ) :
    complexification (M ^ k) = complexification M ^ k :=
  Matrix.map_pow M (algebraMap ℝ ℂ) k

open scoped Matrix.Norms.Operator in
lemma real_power_criterion {n : ℕ} (M : RealMatrix n) :
    (∀ v : Vector n, Tendsto (fun k : ℕ => M ^ k *ᵥ v) atTop (𝓝 0)) ↔ rho M < 1 := by
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
    have hs : spectralRadius ℂ (complexification M) = 0 := by
      simp [spectralRadius, spectrum.of_subsingleton]
    simp only [rho, hs, ENNReal.toReal_zero, zero_lt_one, iff_true]
    intro v
    have he : (fun k : ℕ => M ^ k *ᵥ v) = fun _ => (0 : Vector n) := by
      funext k; exact Subsingleton.elim _ _
    rw [he]
    exact tendsto_const_nhds
  | inr h =>
    have hf : spectralRadius ℂ (complexification M) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top (spectrum.spectralRadius_le_nnnorm _)
    rw [rho, ← ENNReal.toReal_one, ENNReal.toReal_lt_toReal hf ENNReal.one_ne_top,
      ← complex_power_criterion]
    have he (k : ℕ) (i j : Fin n) : (complexification M ^ k) i j = ((M ^ k) i j : ℂ) := by
      rw [← complexification_pow]; rfl
    constructor
    · intro hv
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_pi_nhds.mpr
      intro j
      have ht := tendsto_pi_nhds.mp (hv (Pi.single j 1)) i
      have ht' : Tendsto (fun k : ℕ => (M ^ k) i j) atTop (𝓝 0) := by
        simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using ht
      change Tendsto (fun k : ℕ => (complexification M ^ k) i j) atTop (𝓝 0)
      simp_rw [he]
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp ht'
    · intro hc v
      apply tendsto_pi_nhds.mpr
      intro i
      have ht : ∀ j, Tendsto (fun k : ℕ => (M ^ k) i j) atTop (𝓝 0) := by
        intro j
        have ht := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hc i) j
        change Tendsto (fun k : ℕ => (complexification M ^ k) i j) atTop (𝓝 0) at ht
        simp_rw [he] at ht
        simpa only [Function.comp_def, Complex.ofReal_re, Complex.zero_re] using
          Complex.continuous_re.continuousAt.tendsto.comp ht
      simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero] using
        tendsto_finset_sum Finset.univ (fun j _ => (ht j).mul_const (v j))

lemma convergence_iff {n : ℕ} (A D N : RealMatrix n) (b x : Vector n)
    (hA : A = D + N) (hD : IsUnit D.det) (hx : A *ᵥ x = b) :
    (∀ x₀ : Vector n, Tendsto (iterate A D b x₀) atTop (𝓝 x)) ↔
      rho (iterationMatrix D N) < 1 := by
  have hi (x₀ : Vector n) (k : ℕ) : iterate A D b x₀ k =
      iterationMatrix D N ^ k *ᵥ (x₀ - x) + x := by
    exact sub_eq_iff_eq_add.mp (error_power A D N b x x₀ hA hD hx k)
  rw [← real_power_criterion]
  constructor
  · intro h v
    have ht := (h (v + x)).sub_const x
    simpa only [hi, add_sub_cancel_right, sub_self] using ht
  · intro h x₀
    have ht := (h (x₀ - x)).add_const x
    simpa only [zero_add, ← hi] using ht

lemma norm_suffices {n : ℕ} (M : RealMatrix n) (hM : matrixInfNorm M < 1) :
    ∀ v : Vector n, Tendsto (fun k : ℕ => M ^ k *ᵥ v) atTop (𝓝 0) := by
  intro v
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  change Tendsto (fun k : ℕ => vectorInfNorm (M ^ k *ᵥ v)) atTop (𝓝 0)
  apply squeeze_zero (fun k => NNReal.coe_nonneg _) (fun k => inf_power_le M v k)
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (inf_nonneg M) hM).mul_const (vectorInfNorm v)

/-- Full selected result, with the update equations, both error identities,
both bounds, the spectral-radius criterion for every initial guess, and the
infinity-norm sufficient condition and contraction estimate.

No invertibility of A, positivity, symmetry, or convergence is assumed.
All natural dimensions, including zero, and arbitrary block partitions are allowed.
-/
theorem block_jacobi_real
    {n : ℕ} {B : Type*} (block : Fin n → B)
    (A D N : RealMatrix n) (b x : Vector n)
    (hblocks : IsBlockDecomposition block A D N)
    (hD : IsUnit D.det) (hx : A *ᵥ x = b) :
    (∀ (x₀ : Vector n) (k : ℕ),
      D *ᵥ correction A D b x₀ k = b - A *ᵥ iterate A D b x₀ k ∧
      iterate A D b x₀ (k + 1) = iterate A D b x₀ k + correction A D b x₀ k ∧
      error A D b x x₀ (k + 1) = iterationMatrix D N *ᵥ error A D b x x₀ k ∧
      error A D b x x₀ k = iterationMatrix D N ^ k *ᵥ error A D b x x₀ 0 ∧
      (∀ i, vectorAbs (error A D b x x₀ k) i ≤
        ((matrixAbs (iterationMatrix D N)) ^ k *ᵥ
          vectorAbs (error A D b x x₀ 0)) i) ∧
      vectorInfNorm (error A D b x x₀ k) ≤
        matrixInfNorm (iterationMatrix D N) ^ k *
          vectorInfNorm (error A D b x x₀ 0)) ∧
    rho (iterationMatrix D N) = rho (D⁻¹ * N) ∧
    ((∀ x₀ : Vector n, Tendsto (iterate A D b x₀) atTop (𝓝 x)) ↔
      rho (iterationMatrix D N) < 1) ∧
    (matrixInfNorm (iterationMatrix D N) < 1 →
      (∀ x₀ : Vector n, Tendsto (iterate A D b x₀) atTop (𝓝 x)) ∧
      0 ≤ matrixInfNorm (iterationMatrix D N) ∧
      (∀ u v : Vector n,
        vectorInfNorm (update A D b u - update A D b v) ≤
          matrixInfNorm (iterationMatrix D N) * vectorInfNorm (u - v))) := by
  have hA := hblocks.1
  refine ⟨?_, rho_neg (D⁻¹ * N), convergence_iff A D N b x hA hD hx, ?_⟩
  · intro x₀ k
    refine ⟨?_, rfl, error_step A D N b x x₀ hA hD hx k, ?_, ?_, ?_⟩
    · unfold correction correctionAt
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv D hD, Matrix.one_mulVec]
    · simpa only [error, iterate] using error_power A D N b x x₀ hA hD hx k
    · rw [error_power A D N b x x₀ hA hD hx k]
      simpa only [error, iterate] using abs_power_le (iterationMatrix D N) (x₀ - x) k
    · rw [error_power A D N b x x₀ hA hD hx k]
      simpa only [error, iterate] using inf_power_le (iterationMatrix D N) (x₀ - x) k
  · intro hM
    refine ⟨(convergence_iff A D N b x hA hD hx).mpr
      ((real_power_criterion _).mp (norm_suffices _ hM)), inf_nonneg _, ?_⟩
    intro u v
    rw [update_sub A D N b hA hD]
    exact inf_mulVec_le _ _

end Research.BlockJacobi
