import Mathlib

/-!
Formal statement of `theorem:block_jacobi_real` in /spec/source.txt,
with the proof in /spec/paper.tex, lines 613–693, as mathematical context.

The proof includes the algebraic iteration identities, componentwise and
infinity-norm bounds, and the complex spectral-radius convergence criterion.
-/

noncomputable section

open Filter Matrix
open scoped Topology

namespace Research.BlockJacobi

abbrev Vector (n : ℕ) := Fin n → ℝ
abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Coordinates with the same label form a block. No restriction on block sizes
or positivity of the ambient dimension is imposed. -/
def IsBlockSplitting {n m : ℕ} (block : Fin n → Fin m)
    (A D N : RealMatrix n) : Prop :=
  A = D + N ∧
  (∀ i j, block i ≠ block j → D i j = 0) ∧
  (∀ i j, block i = block j → N i j = 0)

/-- The diagonal blocks of the original input matrix. -/
def diagonalBlocks {n m : ℕ} (block : Fin n → Fin m)
    (A : RealMatrix n) : RealMatrix n :=
  fun i j => if block i = block j then A i j else 0

/-- The off-diagonal blocks of the original input matrix. -/
def offDiagonalBlocks {n m : ℕ} (block : Fin n → Fin m)
    (A : RealMatrix n) : RealMatrix n :=
  A - diagonalBlocks block A

/-- The exact residual at an arbitrary current approximation. -/
def residual {n : ℕ} (A : RealMatrix n) (b u : Vector n) : Vector n :=
  b - A.mulVec u

/-- The correction obtained by solving with the diagonal-block matrix.
Nonsingularity is an explicit assumption of the theorem below. -/
def correction {n : ℕ} (A D : RealMatrix n) (b u : Vector n) : Vector n :=
  D⁻¹.mulVec (residual A b u)

/-- The update-form Jacobi map. -/
def update {n : ℕ} (A D : RealMatrix n) (b u : Vector n) : Vector n :=
  u + correction A D b u

/-- The actual iteration from the supplied initial guess. -/
def iterate {n : ℕ} (A D : RealMatrix n) (b x₀ : Vector n) : ℕ → Vector n
  | 0 => x₀
  | k + 1 => update A D b (iterate A D b x₀ k)

/-- Correction numbered as in the paper; the unused zeroth correction is zero. -/
def correctionSequence {n : ℕ} (A D : RealMatrix n) (b x₀ : Vector n) :
    ℕ → Vector n
  | 0 => 0
  | k + 1 => correction A D b (iterate A D b x₀ k)

/-- Forward error with respect to the specified exact solution. -/
def error {n : ℕ} (A D : RealMatrix n) (b x₀ x : Vector n) (k : ℕ) : Vector n :=
  iterate A D b x₀ k - x

/-- P = -D⁻¹N. -/
def iterationMatrix {n : ℕ} (D N : RealMatrix n) : RealMatrix n :=
  -(D⁻¹ * N)

/-- Entrywise absolute value, distinct from any matrix norm. -/
def matrixAbs {n : ℕ} (M : RealMatrix n) : RealMatrix n :=
  fun i j => |M i j|

/-- Entrywise absolute value of a vector. -/
def vectorAbs {n : ℕ} (v : Vector n) : Vector n := fun i => |v i|

/-- Induced infinity matrix norm: the largest absolute row sum.
The outer Pi norm is the usual finite supremum norm, with value zero in
dimension zero. This definition avoids the default entrywise matrix norm. -/
def matrixInfNorm {n : ℕ} (M : RealMatrix n) : ℝ :=
  ‖fun i => ∑ j, |M i j|‖

/-- Complexification retains the nonreal eigenvalues of a real matrix. -/
def complexify {n : ℕ} (M : RealMatrix n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (M i j : ℂ)

/-- The usual spectral radius, as an extended nonnegative real.
The spectrum is computed over ℂ, including for a real input matrix. -/
def rho {n : ℕ} (M : RealMatrix n) : ENNReal :=
  spectralRadius ℂ (complexify M)

/-- Convergence to the specified exact solution for every initial guess. -/
def ConvergesForEveryInitialGuess {n : ℕ} (A D : RealMatrix n)
    (b x : Vector n) : Prop :=
  ∀ x₀ : Vector n, Tendsto (iterate A D b x₀) atTop (𝓝 x)

lemma update_sub {n} (A D N : RealMatrix n) (b : Vector n)
    (hs : A = D + N) (hd : IsUnit D.det) (u v : Vector n) :
    update A D b u - update A D b v = (iterationMatrix D N).mulVec (u-v) := by
  have hi := Matrix.nonsing_inv_mul D hd
  simp only [update, correction, residual, iterationMatrix, hs, add_mulVec,
    mulVec_sub, mulVec_add, neg_mulVec, mulVec_mulVec, hi, one_mulVec]
  abel

lemma update_fixed {n} (A D : RealMatrix n) (b x : Vector n)
    (hx : A.mulVec x = b) : update A D b x = x := by
  simp [update, correction, residual, hx]

lemma error_step {n} (A D N : RealMatrix n) (b x x₀ : Vector n)
    (hs : A = D + N) (hd : IsUnit D.det) (hx : A.mulVec x = b) (k) :
    error A D b x₀ x (k+1) = (iterationMatrix D N).mulVec (error A D b x₀ x k) := by
  simpa [error, iterate, update_fixed A D b x hx] using
    update_sub A D N b hs hd (iterate A D b x₀ k) x

lemma error_pow {n} (A D N : RealMatrix n) (b x x₀ : Vector n)
    (hs : A = D + N) (hd : IsUnit D.det) (hx : A.mulVec x = b) (k) :
    error A D b x₀ x k = (iterationMatrix D N ^ k).mulVec (x₀-x) := by
  induction k with
  | zero => simp [error, iterate]
  | succ k ih => rw [error_step A D N b x x₀ hs hd hx, ih, mulVec_mulVec, pow_succ']

lemma abs_mulVec {n} (M : RealMatrix n) (v : Vector n) :
    vectorAbs (M.mulVec v) ≤ (matrixAbs M).mulVec (vectorAbs v) := by
  intro i
  simpa [vectorAbs, matrixAbs, mulVec, dotProduct, abs_mul] using
    Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j => M i j * v j)

lemma abs_mono {n} (M : RealMatrix n) (u v : Vector n) (h : u ≤ v) :
    (matrixAbs M).mulVec u ≤ (matrixAbs M).mulVec v := by
  intro i
  change (∑ j, |M i j| * u j) ≤ ∑ j, |M i j| * v j
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (abs_nonneg (M i j))

lemma error_abs {n} (A D N : RealMatrix n) (b x x₀ : Vector n)
    (hs : A = D + N) (hd : IsUnit D.det) (hx : A.mulVec x = b) (k) :
    vectorAbs (error A D b x₀ x k) ≤
      (matrixAbs (iterationMatrix D N) ^ k).mulVec (vectorAbs (x₀-x)) := by
  induction k with
  | zero => simp [error, iterate]
  | succ k ih =>
    rw [error_step A D N b x x₀ hs hd hx, pow_succ', ← mulVec_mulVec]
    exact (abs_mulVec _ _).trans (abs_mono _ _ _ ih)

lemma inf_bound {n} (M : RealMatrix n) (v : Vector n) :
    ‖M.mulVec v‖ ≤ matrixInfNorm M * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro i
  calc
    ‖M.mulVec v i‖ ≤ ∑ j, |M i j| * |v j| := by
      simpa [mulVec, dotProduct, Real.norm_eq_abs, abs_mul] using
        Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j => M i j * v j)
    _ ≤ ∑ j, |M i j| * ‖v‖ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v j) (abs_nonneg _)
    _ = (∑ j, |M i j|) * ‖v‖ := (Finset.sum_mul ..).symm
    _ ≤ matrixInfNorm M * ‖v‖ := mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (by
        simpa [matrixInfNorm, Real.norm_eq_abs] using
          (norm_le_pi_norm (fun i => ∑ j, |M i j|) i))) (norm_nonneg _)

lemma error_norm {n} (A D N : RealMatrix n) (b x x₀ : Vector n)
    (hs : A = D + N) (hd : IsUnit D.det) (hx : A.mulVec x = b) (k) :
    ‖error A D b x₀ x k‖ ≤ matrixInfNorm (iterationMatrix D N)^k * ‖x₀-x‖ := by
  induction k with
  | zero => simp [error, iterate]
  | succ k ih =>
    rw [error_step A D N b x x₀ hs hd hx, pow_succ']
    exact (inf_bound _ _).trans (by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left ih (norm_nonneg _))

lemma rho_neg {n} (M : RealMatrix n) : rho (-M) = rho M := by
  have hc : complexify (-M) = -complexify M := by ext i j; simp [complexify]
  unfold rho
  rw [hc, spectralRadius, ← spectrum.neg_eq]
  simp only [Set.mem_neg]
  exact Equiv.neg ℂ |>.iSup_congr (fun k => by simp)


section Spectral
open scoped Matrix.Norms.Operator

lemma complexify_pow {n} (M : RealMatrix n) (k : ℕ) :
    complexify (M^k) = complexify M ^ k :=
  Matrix.map_pow M Complex.ofRealHom k

lemma complex_powers_decay {n} (M : Matrix (Fin n) (Fin n) ℂ)
    (h : spectralRadius ℂ M < 1) : Tendsto (fun k : ℕ => M^k) atTop (𝓝 0) := by
  have hf : spectralRadius ℂ M ≠ ⊤ := ne_of_lt (h.trans ENNReal.one_lt_top)
  have hr := (ENNReal.tendsto_toReal hf).comp
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius M)
  simp only [Function.comp_def, ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] at hr
  have hreal : (spectralRadius ℂ M).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hf ENNReal.one_ne_top).mpr h
  obtain ⟨q, hq, hq1⟩ := exists_between hreal
  have hq0 : 0 ≤ q := (ENNReal.toReal_nonneg).trans hq.le
  have he := hr.eventually (gt_mem_nhds hq)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall fun k => norm_nonneg (M^k)) _
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
  filter_upwards [he, eventually_gt_atTop 0] with k hk hk0
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk0
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg (M^k)) _) hk.le (le_of_lt hkpos)
  simpa [← Real.rpow_mul (norm_nonneg (M^k)), one_div, inv_mul_cancel₀ hkpos.ne', Real.rpow_natCast] using hh

lemma real_powers_iff {n} (M : RealMatrix n) :
    (∀ v : Vector n, Tendsto (fun k : ℕ => (M^k).mulVec v) atTop (𝓝 0)) ↔ rho M < 1 := by
  by_cases hn : n = 0
  · subst n
    have hall : ∀ k : ℕ, M^k = 0 := fun _ => Subsingleton.elim _ _
    simp [hall, rho, show complexify M = 0 from Subsingleton.elim _ _]
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  constructor
  · intro h
    have he : Tendsto (fun k : ℕ => complexify M ^ k) atTop (𝓝 0) := by
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_pi_nhds.mpr
      intro j
      have hv := ((tendsto_pi_nhds.mp (h (Pi.single j 1))) i)
      have hv' : Tendsto (fun k : ℕ => (M^k) i j) atTop (𝓝 0) := by
        simpa only [Matrix.mulVec_single_one] using hv
      simpa [← complexify_pow, complexify] using (Complex.continuous_ofReal.tendsto 0).comp hv'
    have hn : Tendsto (fun k : ℕ => (‖complexify M ^ k‖₊ : ENNReal)) atTop (𝓝 0) := by
      simpa using ENNReal.continuous_coe.continuousAt.tendsto.comp he.nnnorm
    have hp : Tendsto (fun k : ℕ => rho M ^ k) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hn
      · exact Filter.Eventually.of_forall fun _ => bot_le
      · filter_upwards [eventually_ne_atTop 0] with k hk
        exact (spectrum.spectralRadius_pow_le (𝕜 := ℂ) (complexify M) k hk).trans
          (spectrum.spectralRadius_le_nnnorm _)
    exact ENNReal.tendsto_pow_atTop_nhds_zero_iff.mp hp
  · intro h v
    have he := complex_powers_decay (complexify M) h
    apply tendsto_pi_nhds.mpr
    intro i
    have hij (j) : Tendsto (fun k : ℕ => (M^k) i j) atTop (𝓝 0) := by
      have hc := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp he i) j)
      simpa [← complexify_pow, complexify] using Complex.continuous_re.continuousAt.tendsto.comp hc
    simpa [Matrix.mulVec, dotProduct] using tendsto_finset_sum Finset.univ
      (fun j _ => (hij j).mul_const (v j))

end Spectral

/-- Full update-form block-Jacobi theorem in exact real arithmetic.

The only hypotheses are the block splitting, nonsingularity of D, and Ax=b.
In particular, neither nonsingularity of A nor a convergence criterion is
assumed. The conclusions include the actual correction/update equations,
uniqueness of any sequence satisfying these equations, exact error identities,
componentwise and infinity-norm bounds, the spectral-radius characterization,
and convergence and contraction under the sufficient infinity-norm condition.
-/
theorem block_jacobi_real
    {n m : ℕ} (block : Fin n → Fin m)
    (A D N : RealMatrix n) (b x : Vector n)
    (hblocks : IsBlockSplitting block A D N)
    (hD : IsUnit D.det)
    (hsol : A.mulVec x = b) :
    let P := iterationMatrix D N
    -- The block model is exactly the diagonal/off-diagonal decomposition of A.
    (D = diagonalBlocks block A ∧ N = offDiagonalBlocks block A) ∧
    -- The constructed iteration solves the correction system and performs the update.
    (∀ x₀ : Vector n,
      iterate A D b x₀ 0 = x₀ ∧
      ∀ k : ℕ,
        D.mulVec (correctionSequence A D b x₀ (k + 1)) =
          b - A.mulVec (iterate A D b x₀ k) ∧
        iterate A D b x₀ (k + 1) =
          iterate A D b x₀ k + correctionSequence A D b x₀ (k + 1)) ∧
    -- Thus the result also applies to every exact sequence specified in the source.
    (∀ (x₀ : Vector n) (X C : ℕ → Vector n),
      X 0 = x₀ →
      (∀ k, D.mulVec (C (k + 1)) = b - A.mulVec (X k)) →
      (∀ k, X (k + 1) = X k + C (k + 1)) →
      (∀ k, X k = iterate A D b x₀ k) ∧
      (∀ k, C (k + 1) = correctionSequence A D b x₀ (k + 1))) ∧
    -- Error recursion and its two distinct quantitative bounds.
    (∀ (x₀ : Vector n) (k : ℕ),
      error A D b x₀ x (k + 1) = P.mulVec (error A D b x₀ x k) ∧
      error A D b x₀ x k = (P ^ k).mulVec (error A D b x₀ x 0) ∧
      vectorAbs (error A D b x₀ x k) ≤
        (matrixAbs P ^ k).mulVec (vectorAbs (error A D b x₀ x 0)) ∧
      ‖error A D b x₀ x k‖ ≤
        matrixInfNorm P ^ k * ‖error A D b x₀ x 0‖) ∧
    -- The sign does not affect the usual complex spectral radius.
    rho P = rho (D⁻¹ * N) ∧
    (ConvergesForEveryInitialGuess A D b x ↔ rho P < 1) ∧
    -- Lipschitz estimate for the update map, with the stated contraction factor.
    (∀ u v : Vector n,
      ‖update A D b u - update A D b v‖ ≤ matrixInfNorm P * ‖u - v‖) ∧
    (matrixInfNorm P < 1 →
      ConvergesForEveryInitialGuess A D b x ∧
      ∃ q : NNReal, (q : ℝ) = matrixInfNorm P ∧ q < 1 ∧
        LipschitzWith q (update A D b)) := by
  dsimp only
  have hs := hblocks.1
  have hcor (u : Vector n) : D.mulVec (correction A D b u) = b - A.mulVec u := by
    simp [correction, residual, mulVec_mulVec, Matrix.mul_nonsing_inv D hD]
  have huniq (u c : Vector n) (h : D.mulVec c = b - A.mulVec u) :
      c = correction A D b u := by
    rw [correction, residual, ← h, mulVec_mulVec, Matrix.nonsing_inv_mul D hD, one_mulVec]
  have hconvnorm (h : matrixInfNorm (iterationMatrix D N) < 1) :
      ConvergesForEveryInitialGuess A D b x := by
    intro x₀
    have he : Tendsto (fun k => error A D b x₀ x k) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      apply squeeze_zero (fun _ => norm_nonneg _) (error_norm A D N b x x₀ hs hD hsol)
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h).mul_const ‖x₀-x‖
    simpa [error] using he.add_const x
  refine ⟨?_, ?_, ?_, ?_, rho_neg (D⁻¹ * N), ?_, ?_, ?_⟩
  · have hd : D = diagonalBlocks block A := by
      ext i j
      have hij := congrFun (congrFun hs i) j
      by_cases h : block i = block j
      · simpa [diagonalBlocks, h, hblocks.2.2 i j h] using hij.symm
      · simp [diagonalBlocks, h, hblocks.2.1 i j h]
    exact ⟨hd, by rw [offDiagonalBlocks, ← hd, hs]; abel⟩
  · intro x₀
    exact ⟨rfl, fun k => ⟨hcor _, rfl⟩⟩
  · intro x₀ X C h0 hc hu
    have hi : ∀ k, X k = iterate A D b x₀ k := by
      intro k
      induction k with
      | zero => exact h0
      | succ k ih => rw [hu, huniq _ _ (hc k), ih]; rfl
    exact ⟨hi, fun k => by rw [huniq _ _ (hc k), hi]; rfl⟩
  · intro x₀ k
    exact ⟨error_step A D N b x x₀ hs hD hsol k,
      by simpa [error, iterate] using error_pow A D N b x x₀ hs hD hsol k,
      by simpa [error, iterate] using error_abs A D N b x x₀ hs hD hsol k,
      by simpa [error, iterate] using error_norm A D N b x x₀ hs hD hsol k⟩
  · constructor
    · intro hc
      apply (real_powers_iff (iterationMatrix D N)).mp
      intro v
      have he := (hc (x+v)).sub_const x
      change Tendsto (fun k => error A D b (x+v) x k) atTop (𝓝 (x-x)) at he
      simpa only [sub_self, error_pow A D N b x (x+v) hs hD hsol,
        add_sub_cancel_left] using he
    · intro hr x₀
      have he := (real_powers_iff (iterationMatrix D N)).mpr hr (x₀-x)
      have he' : Tendsto (fun k => error A D b x₀ x k) atTop (𝓝 0) := by
        simpa only [error_pow A D N b x x₀ hs hD hsol] using he
      simpa [error] using he'.add_const x
  · intro u v
    rw [update_sub A D N b hs hD]
    exact inf_bound _ _
  · intro h
    refine ⟨hconvnorm h, ⟨⟨matrixInfNorm (iterationMatrix D N), norm_nonneg _⟩, rfl, h, ?_⟩⟩
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simpa [dist_eq_norm, update_sub A D N b hs hD] using
      inf_bound (iterationMatrix D N) (u-v)

end Research.BlockJacobi
