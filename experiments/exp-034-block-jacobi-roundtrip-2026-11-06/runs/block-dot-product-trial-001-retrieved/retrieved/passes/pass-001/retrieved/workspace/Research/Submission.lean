import Mathlib

/-!
Formal statement of Bhola, `theorem:block_dot_product` (source.txt;
paper.tex, lines 235–291). Indices in the implementation are zero based.

No overflow/underflow is represented by the standard relative-error model
at every executed operation. `RoundingErrors` supplies those local errors;
`Admissible` bounds only errors at operations that are actually executed.
No expansion of the computed answer or global error bound is assumed.

The implicit algorithmic requirement is `0 < T`. We also support n = 0:
there are no blocks, the depth is zero, and the computed answer is zero.
For positive block counts, `Nat.clog 2` is the ceiling base-two logarithm
(see `Nat.clog_le_iff_le_pow`). The tree pads its leaves to a power of two.
-/

namespace Research.BlockDotProduct

/-- The number of blocks, namely ceil(n/T) when T > 0. -/
def blockCount (n T : ℕ) : ℕ := (n + T - 1) / T

/-- Ceiling binary logarithm of the block count; zero for zero blocks. -/
def treeDepth (n T : ℕ) : ℕ := Nat.clog 2 (blockCount n T)

/-- The source's deterministic error constant. -/
noncomputable def gamma (u : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) * u / (1 - (k : ℝ) * u)

/-- Zero extension, including the unused entries of the final block. -/
def padded {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then x ⟨i, h⟩ else 0

/-- Local relative errors. `mul j t` belongs to product t of block j;
`add j t` belongs to adding product t to the preceding accumulator (t > 0).
`tree h j` belongs to node j at height h+1 above the leaves. -/
structure RoundingErrors where
  mul : ℕ → ℕ → ℝ
  add : ℕ → ℕ → ℝ
  tree : ℕ → ℕ → ℝ

/-- Admissibility expresses the local floating-point model on the execution.
There are no bounds required on unused tape entries. -/
def Admissible (u : ℝ) (n T : ℕ) (e : RoundingErrors) : Prop :=
  (∀ j < blockCount n T, ∀ t < T, |e.mul j t| ≤ u) ∧
  (∀ j < blockCount n T, ∀ t < T, 0 < t → |e.add j t| ≤ u) ∧
  (∀ h < treeDepth n T, ∀ j < 2 ^ (treeDepth n T - (h + 1)),
    |e.tree h j| ≤ u)

/-- One rounded multiplication of padded original entries. -/
def roundedProduct {n : ℕ} (T : ℕ) (x y : Fin n → ℝ)
    (e : RoundingErrors) (j t : ℕ) : ℝ :=
  (padded x (j * T + t) * padded y (j * T + t)) * (1 + e.mul j t)

/-- Sequential evaluation of the first k products in block j. The first
product seeds the accumulator, so there is no spurious rounded addition
to zero. Calling this with k = T computes a complete block. -/
def sequentialBlock {n : ℕ} (T : ℕ) (x y : Fin n → ℝ)
    (e : RoundingErrors) (j : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
    if k = 0 then roundedProduct T x y e j k
    else (sequentialBlock T x y e j k + roundedProduct T x y e j k) *
      (1 + e.add j k)

/-- Real block results followed by zero leaves up to the tree capacity. -/
def blockLeaf {n : ℕ} (T : ℕ) (x y : Fin n → ℝ)
    (e : RoundingErrors) (j : ℕ) : ℝ :=
  if j < blockCount n T then sequentialBlock T x y e j T else 0

/-- A complete binary reduction: node j at height h covers the consecutive
leaves j*2^h through (j+1)*2^h-1. Each internal node performs one locally
rounded addition. -/
def binaryReduction (e : RoundingErrors) (leaf : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, j => leaf j
  | h + 1, j =>
    (binaryReduction e leaf h (2 * j) + binaryReduction e leaf h (2 * j + 1)) *
      (1 + e.tree h j)

/-- The actual two-stage computed dot product, rather than an arbitrary
weighted sum of exact input products. -/
def computed {n : ℕ} (T : ℕ) (x y : Fin n → ℝ) (e : RoundingErrors) : ℝ :=
  binaryReduction e (blockLeaf T x y e) (treeDepth n T) 0

private def Stable (u : ℝ) (k : ℕ) (a b m : ℝ) : Prop :=
  0 ≤ m ∧ |b| ≤ m ∧ |a - b| ≤ ((1 + u)^k - 1) * m

private lemma stable_exact (u : ℝ) (hu : 0 ≤ u) (k : ℕ) (b : ℝ) :
    Stable u k b b |b| := by
  refine ⟨abs_nonneg _, le_rfl, ?_⟩
  simp only [sub_self, abs_zero]
  exact mul_nonneg (sub_nonneg.mpr (one_le_pow₀ (by linarith))) (abs_nonneg _)

private lemma stable_mono {u a b m : ℝ} (hu : 0 ≤ u) {k l : ℕ}
    (h : Stable u k a b m) (hkl : k ≤ l) : Stable u l a b m := by
  refine ⟨h.1, h.2.1, h.2.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (sub_le_sub_right (pow_le_pow_right₀ (by linarith) hkl) _) h.1

private lemma stable_round {u a b m δ : ℝ} (hu : 0 ≤ u) {k : ℕ}
    (h : Stable u k a b m) (hd : |δ| ≤ u) :
    Stable u (k+1) (a * (1+δ)) b m := by
  refine ⟨h.1, h.2.1, ?_⟩
  have ha : |a| ≤ (1+u)^k * m := by
    have hh := abs_add_le (a-b) b
    rw [sub_add_cancel] at hh
    nlinarith [h.2.2, h.2.1]
  have hh : |a*(1+δ)-b| ≤ |a-b| + |a| * |δ| := by
    calc
      _ = |(a-b)+a*δ| := by congr 1; ring
      _ ≤ _ := by simpa [abs_mul] using abs_add_le (a-b) (a*δ)
  have hm := mul_le_mul ha hd (abs_nonneg δ) (mul_nonneg (pow_nonneg (by linarith) _) h.1)
  rw [pow_succ]
  nlinarith [h.2.2]

private lemma stable_add {u a b m a' b' m' : ℝ} {k : ℕ}
    (h : Stable u k a b m) (h' : Stable u k a' b' m') :
    Stable u k (a+a') (b+b') (m+m') := by
  refine ⟨add_nonneg h.1 h'.1, (abs_add_le _ _).trans (add_le_add h.2.1 h'.2.1), ?_⟩
  calc
    |a+a'-(b+b')| = |(a-b)+(a'-b')| := by congr 1; ring
    _ ≤ |a-b|+|a'-b'| := abs_add_le _ _
    _ ≤ _ := by nlinarith [h.2.2, h'.2.2]

private lemma pow_gamma {u : ℝ} (hu : 0 ≤ u) (k : ℕ) (hk : (k:ℝ)*u < 1) :
    (1+u)^k - 1 ≤ gamma u k := by
  have hp : (1+u)^k * (1-(k:ℝ)*u) ≤ 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      have hn : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
      have hp : 0 ≤ (1+u)^k := pow_nonneg (by linarith) _
      have ih := ih (by rw [Nat.cast_add, Nat.cast_one] at hk; nlinarith)
      nlinarith [mul_nonneg hp (mul_nonneg hn (sq_nonneg u))]
  unfold gamma
  apply (le_div_iff₀ (by linarith : 0 < 1-(k:ℝ)*u)).mpr
  nlinarith

private def exactBlock {n : ℕ} (T : ℕ) (x y : Fin n → ℝ) (j k : ℕ) : ℝ :=
  ∑ t ∈ Finset.range k, padded x (j*T+t) * padded y (j*T+t)

private def massBlock {n : ℕ} (T : ℕ) (x y : Fin n → ℝ) (j k : ℕ) : ℝ :=
  ∑ t ∈ Finset.range k, |padded x (j*T+t) * padded y (j*T+t)|

private lemma block_stable {n T : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (x y : Fin n → ℝ) (e : RoundingErrors) (he : Admissible u n T e)
    (j : ℕ) (hj : j < blockCount n T) (k : ℕ) (hk : k ≤ T) :
    Stable u k (sequentialBlock T x y e j k)
      (exactBlock T x y j k) (massBlock T x y j k) := by
  induction k with
  | zero => simp [sequentialBlock, exactBlock, massBlock, Stable]
  | succ k ih =>
    have hm := he.1 j hj k (by omega)
    have hp := stable_round hu (stable_exact u hu 0
      (padded x (j*T+k)*padded y (j*T+k))) hm
    simp only [sequentialBlock]
    by_cases hz : k = 0
    · subst k
      simpa [exactBlock, massBlock, roundedProduct] using hp
    · rw [if_neg hz]
      simpa [exactBlock, massBlock, Finset.sum_range_succ, roundedProduct] using
        stable_round hu (stable_add (ih (by omega))
          (stable_mono hu hp (by omega : 1 ≤ k)))
          (he.2.1 j hj k (by omega) (by omega))

private def treeSum (leaf : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, j => leaf j
  | h+1, j => treeSum leaf h (2*j) + treeSum leaf h (2*j+1)

private lemma tree_stable {u : ℝ} (hu : 0 ≤ u) (e : RoundingErrors)
    (a b m : ℕ → ℝ) (K d : ℕ)
    (hl : ∀ j < 2^d, Stable u K (a j) (b j) (m j))
    (he : ∀ h < d, ∀ j < 2^(d-(h+1)), |e.tree h j| ≤ u)
    (h : ℕ) (hh : h ≤ d) (j : ℕ) (hj : j < 2^(d-h)) :
    Stable u (K+h) (binaryReduction e a h j) (treeSum b h j) (treeSum m h j) := by
  induction h generalizing j with
  | zero => simpa [binaryReduction, treeSum] using hl j (by simpa using hj)
  | succ h ih =>
    have hpow : 2^(d-h) = 2^(d-(h+1))*2 := by
      rw [show d-h = (d-(h+1))+1 by omega, pow_succ]
    have h1 : 2*j < 2^(d-h) := by rw [hpow]; omega
    have h2 : 2*j+1 < 2^(d-h) := by rw [hpow]; omega
    simpa [binaryReduction, treeSum, Nat.add_assoc] using
      stable_round hu (stable_add (ih (by omega) _ h1) (ih (by omega) _ h2))
        (he h (by omega) j hj)

private lemma treeSum_eq (f : ℕ → ℝ) (h j : ℕ) :
    treeSum f h j = ∑ t ∈ Finset.range (2^h), f (j*2^h+t) := by
  induction h generalizing j with
  | zero => simp [treeSum]
  | succ h ih =>
    rw [treeSum, ih, ih, show 2^(h+1) = 2^h+2^h by rw [pow_succ]; omega,
      Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl; intro t ht; congr 1; ring
    · apply Finset.sum_congr rfl; intro t ht; congr 1; ring

private lemma sum_blocks (f : ℕ → ℝ) (T b : ℕ) :
    (∑ j ∈ Finset.range b, ∑ t ∈ Finset.range T, f (j*T+t)) =
      ∑ i ∈ Finset.range (b*T), f i := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]

private lemma coverage {n T : ℕ} (hT : 0 < T) : n ≤ blockCount n T * T := by
  have h := Nat.lt_mul_div_succ (n+T-1) hT
  unfold blockCount
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm T] at h
  omega

private lemma layout_sum {n T : ℕ} (hT : 0 < T) (f : ℕ → ℝ)
    (hf : ∀ i, n ≤ i → f i = 0) :
    treeSum (fun j => if j < blockCount n T then
      ∑ t ∈ Finset.range T, f (j*T+t) else 0) (treeDepth n T) 0 =
      ∑ i ∈ Finset.range n, f i := by
  rw [treeSum_eq]
  simp only [Nat.zero_mul, Nat.zero_add]
  have hb : blockCount n T ≤ 2^treeDepth n T := Nat.le_pow_clog (by decide) _
  calc
    _ = ∑ j ∈ Finset.range (blockCount n T), ∑ t ∈ Finset.range T, f (j*T+t) := by
      symm
      calc
        _ = ∑ j ∈ Finset.range (blockCount n T),
            (if j < blockCount n T then ∑ t ∈ Finset.range T, f (j*T+t) else 0) := by
          apply Finset.sum_congr rfl; intro j hj
          rw [if_pos (Finset.mem_range.mp hj)]
        _ = _ := Finset.sum_subset (Finset.range_mono hb) (by
          intro j hj hj'; simp only [Finset.mem_range] at hj'; simp [hj'])
    _ = ∑ i ∈ Finset.range (blockCount n T*T), f i := sum_blocks _ _ _
    _ = _ := (Finset.sum_subset (Finset.range_mono (coverage hT)) (by
      intro i hi hi'; exact hf i (by simpa using hi'))).symm

private lemma padded_sum {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i ∈ Finset.range n, padded x i * padded y i) = ∑ i : Fin n, x i*y i := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl; intro i hi
  simp [padded]

private lemma padded_mass {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i ∈ Finset.range n, |padded x i * padded y i|) = ∑ i : Fin n, |x i*y i| := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl; intro i hi
  simp [padded]

private lemma computed_stable {n T : ℕ} (hT : 0 < T) {u : ℝ} (hu : 0 ≤ u)
    (x y : Fin n → ℝ) (e : RoundingErrors) (he : Admissible u n T e) :
    Stable u (T+treeDepth n T) (computed T x y e)
      (∑ i : Fin n, x i*y i) (∑ i : Fin n, |x i*y i|) := by
  let b := fun j => if j < blockCount n T then exactBlock T x y j T else 0
  let m := fun j => if j < blockCount n T then massBlock T x y j T else 0
  have hs := tree_stable hu e (blockLeaf T x y e) b m T (treeDepth n T)
    (by
      intro j hj
      by_cases h : j < blockCount n T
      · simpa [blockLeaf, b, m, h] using block_stable hu x y e he j h T le_rfl
      · simpa [blockLeaf, b, m, h] using stable_exact u hu T 0)
    he.2.2 (treeDepth n T) le_rfl 0 (by simp)
  have hb : treeSum b (treeDepth n T) 0 = ∑ i : Fin n, x i*y i := by
    rw [← padded_sum]
    exact layout_sum hT (fun i => padded x i * padded y i) (by intro i hi; simp [padded, not_lt.mpr hi])
  have hm : treeSum m (treeDepth n T) 0 = ∑ i : Fin n, |x i*y i| := by
    rw [← padded_mass]
    exact layout_sum hT (fun i => |padded x i * padded y i|) (by intro i hi; simp [padded, not_lt.mpr hi])
  simpa [computed, hb, hm] using hs

private noncomputable def sg (a : ℝ) : ℝ := if 0 ≤ a then 1 else -1

private lemma sg_mul (a : ℝ) : sg a * a = |a| := by
  unfold sg
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

private lemma abs_sg (a : ℝ) : |sg a| = 1 := by
  unfold sg; split_ifs <;> norm_num

/-- Full Block Dot Product theorem: both backward representations hold for
every execution satisfying the local rounding model. The common budget is
exactly T + ceil(log₂(ceil(n/T))), as in the selected source statement. -/
theorem block_dot_product
    {n T : ℕ} (hT : 0 < T) (u : ℝ) (hu : 0 ≤ u)
    (x y : Fin n → ℝ) (e : RoundingErrors)
    (he : Admissible u n T e)
    (hbudget : ((T + treeDepth n T : ℕ) : ℝ) * u < 1) :
    ∃ Δx Δy : Fin n → ℝ,
      (computed T x y e = ∑ i : Fin n, (x i + Δx i) * y i) ∧
      (∀ i, |Δx i| ≤ gamma u (T + treeDepth n T) * |x i|) ∧
      (computed T x y e = ∑ i : Fin n, x i * (y i + Δy i)) ∧
      (∀ i, |Δy i| ≤ gamma u (T + treeDepth n T) * |y i|) := by
  classical
  let S : ℝ := ∑ i : Fin n, x i*y i
  let M : ℝ := ∑ i : Fin n, |x i*y i|
  let E := computed T x y e - S
  let r := E / M
  have hs := computed_stable hT hu x y e he
  have hM : 0 ≤ M := hs.1
  have hg : 0 ≤ gamma u (T+treeDepth n T) := by
    unfold gamma
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)
  have hE : |E| ≤ gamma u (T+treeDepth n T) * M :=
    hs.2.2.trans (mul_le_mul_of_nonneg_right (pow_gamma hu _ hbudget) hM)
  have hr : |r| ≤ gamma u (T+treeDepth n T) := by
    by_cases hz : M = 0
    · simpa [r, hz] using hg
    · dsimp [r]
      rw [abs_div, abs_of_pos (lt_of_le_of_ne hM (Ne.symm hz))]
      exact (div_le_iff₀ (lt_of_le_of_ne hM (Ne.symm hz))).mpr hE
  have hrM : r*M = E := by
    by_cases hz : M = 0
    · have hez : E = 0 := abs_eq_zero.mp (le_antisymm (by simpa [hz] using hE) (abs_nonneg _))
      simp [hz, hez]
    · exact div_mul_cancel₀ E hz
  refine ⟨(fun i => r * |x i| * sg (y i)), (fun i => r * sg (x i) * |y i|), ?_, ?_, ?_, ?_⟩
  · have hh : ∀ i : Fin n, (x i + r * |x i| * sg (y i)) * y i =
        x i*y i + r * |x i*y i| := by
      intro i
      rw [abs_mul, ← sg_mul (y i)]
      ring
    simp_rw [hh]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    change computed T x y e = S + r*M
    rw [hrM]
    dsimp [E]
    ring
  · intro i
    simpa [abs_mul, abs_sg, abs_abs] using mul_le_mul_of_nonneg_right hr (abs_nonneg (x i))
  · have hh : ∀ i : Fin n, x i * (y i + r * sg (x i) * |y i|) =
        x i*y i + r * |x i*y i| := by
      intro i
      rw [abs_mul, ← sg_mul (x i)]
      ring
    simp_rw [hh]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    change computed T x y e = S + r*M
    rw [hrM]
    dsimp [E]
    ring
  · intro i
    simpa [abs_mul, abs_sg, abs_abs] using mul_le_mul_of_nonneg_right hr (abs_nonneg (y i))

end Research.BlockDotProduct
