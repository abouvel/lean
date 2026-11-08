import Mathlib

/-!
Formal statement of `theorem:block_matrix_vector_product` in /spec/source.txt.

This file defines the actual two-stage sequential computation. An error schedule
records the relative error of each multiplication and addition independently;
`Admissible` is precisely the elementary rounding model on executed operations.
Thus no overflow/underflow is represented by the validity of this model, rather
than by any assumed bound on the final output. The schedule may vary by row,
block, and slot, and no algorithmic backward-error bound is a hypothesis.

Block sizes are positive natural numbers and unit roundoff is nonnegative.
Dimensions may be zero; an empty reduction returns zero. Nonempty reductions
start with their first term, without performing an addition to zero.
-/

namespace BlockMatrixVector

/-- Exact natural-number version of `ceil (n / T)` for positive `T`. -/
def blockCount (n T : ℕ) : ℕ := (n + T - 1) / T

/-- The number of rounding factors allowed by the source theorem. -/
def errorCount (n T : ℕ) : ℕ := T + blockCount n T - 1

/-- The source error constant, with a natural index and real unit roundoff. -/
noncomputable def gamma (k : ℕ) (u : ℝ) : ℝ :=
  (k : ℝ) * u / (1 - (k : ℝ) * u)

/-- Slot `t` of block `r` corresponds to original column `r*T+t`. -/
def slotIndex (T r t : ℕ) : ℕ := r * T + t

/-- Extend a finite real vector by zero at every index beyond its dimension. -/
def zeroPad {n : ℕ} (v : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then v ⟨j, h⟩ else 0

/-- Relative errors for every potentially executed operation. Unused indices
have no effect on the computation and carry no admissibility restrictions. -/
structure Roundoff (m : ℕ) where
  mulError : Fin m → ℕ → ℕ → ℝ
  innerError : Fin m → ℕ → ℕ → ℝ
  outerError : Fin m → ℕ → ℝ

/-- The standard relative rounding model on precisely the executed operations.
There is one multiplication per padded slot, additions at slots `1,...,T-1`,
and outer additions at blocks `1,...,blockCount n T - 1`. -/
def Admissible {m : ℕ} (n T : ℕ) (u : ℝ) (e : Roundoff m) : Prop :=
  (∀ (i : Fin m) (r t : ℕ), r < blockCount n T → t < T →
    |e.mulError i r t| ≤ u) ∧
  (∀ (i : Fin m) (r t : ℕ), r < blockCount n T → 1 ≤ t → t < T →
    |e.innerError i r t| ≤ u) ∧
  (∀ (i : Fin m) (r : ℕ), 1 ≤ r → r < blockCount n T →
    |e.outerError i r| ≤ u)

/-- Sequential rounded summation of `length` terms. The first term initializes
the accumulator exactly; subsequent additions use their own relative error.
The multiplication roundings of the terms are handled separately. -/
def sequentialSum (term err : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => term 0
  | k + 2 => (sequentialSum term err (k + 1) + term (k + 1)) *
      (1 + err (k + 1))

/-- One rounded product of the original inputs, with zero padding. -/
def roundedProduct {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (T : ℕ) (e : Roundoff m)
    (i : Fin m) (r t : ℕ) : ℝ :=
  (zeroPad (A i) (slotIndex T r t) * zeroPad x (slotIndex T r t)) *
    (1 + e.mulError i r t)

/-- A block dot product: `T` rounded multiplications followed by sequential
accumulation with `T-1` rounded additions when `T` is positive. -/
def blockPartial {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (T : ℕ) (e : Roundoff m)
    (i : Fin m) (r : ℕ) : ℝ :=
  sequentialSum (roundedProduct A x T e i r) (e.innerError i r) T

/-- The computed vector: sequential accumulation of the block partial sums
for each row. This definition fixes the actual algorithm independently of
the perturbation constructed below. -/
def computedVector {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (T : ℕ) (e : Roundoff m) : Fin m → ℝ :=
  fun i => sequentialSum (blockPartial A x T e i) (e.outerError i)
    (blockCount n T)

/-- Factors from sequential additions affecting a term at position `p` in a
reduction of length `length`. Position zero first participates in addition 1;
position `p>0` first participates in addition `p`. -/
def additionFactor (err : ℕ → ℝ) (length p : ℕ) : ℝ :=
  ∏ k ∈ Finset.Ico (max 1 p) length, (1 + err k)

/-- Full multiplicative coefficient of an original matrix entry in the
computed dot product, using its unique block and slot. -/
def entryFactor {m : ℕ} (n T : ℕ) (e : Roundoff m)
    (i : Fin m) (j : Fin n) : ℝ :=
  (1 + e.mulError i (j.val / T) (j.val % T)) *
    additionFactor (e.innerError i (j.val / T)) T (j.val % T) *
    additionFactor (e.outerError i) (blockCount n T) (j.val / T)

/-- Explicit backward perturbation of the original matrix, without dividing
by any input entry or dot product. It is independent of the vector `x`. -/
def perturbation {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (T : ℕ) (e : Roundoff m) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => A i j * (entryFactor n T e i j - 1)

lemma gamma_mono {a b : ℕ} {u : ℝ} (hu : 0 ≤ u) (hab : a ≤ b)
    (hb : (b : ℝ) * u < 1) : gamma a u ≤ gamma b u := by
  have hab' : (a : ℝ) * u ≤ (b : ℝ) * u := mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hu
  unfold gamma
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith

lemma gamma_step {k : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (hk : ((k + 1 : ℕ) : ℝ) * u < 1) :
    gamma k u * (1 + u) + u ≤ gamma (k + 1) u := by
  push_cast at hk
  have hku : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hd : 0 < 1 - (k : ℝ) * u := by nlinarith
  have heq : gamma k u * (1 + u) + u = ((k : ℝ) * u + u) / (1 - (k : ℝ) * u) := by
    unfold gamma
    field_simp
    ring
  rw [heq]
  unfold gamma
  push_cast
  apply (div_le_div_iff₀ hd (by nlinarith)).2
  nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) * u + u by positivity) hu]

lemma list_gamma (l : List ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hl : ∀ d ∈ l, |d| ≤ u) (hs : (l.length : ℝ) * u < 1) :
    |(l.map (fun d => 1 + d)).prod - 1| ≤ gamma l.length u := by
  induction l with
  | nil => simp [gamma]
  | cons d l ih =>
    have hd := hl d (by simp)
    have hlen : (l.length : ℝ) * u < 1 := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hs; nlinarith
    have hi := ih (fun a ha => hl a (by simp [ha])) hlen
    have hab : |1 + d| ≤ 1 + u := (abs_add_le 1 d).trans (by simpa using hd)
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    calc
      |(1 + d) * (l.map (fun d => 1 + d)).prod - 1| =
          |((l.map (fun d => 1 + d)).prod - 1) * (1 + d) + d| := by congr 1; ring
      _ ≤ |(l.map (fun d => 1 + d)).prod - 1| * |1 + d| + |d| := by
        simpa only [abs_mul] using abs_add_le (((l.map (fun d => 1 + d)).prod - 1) * (1 + d)) d
      _ ≤ gamma l.length u * (1 + u) + u := by
        exact add_le_add (mul_le_mul hi hab (abs_nonneg _) (by unfold gamma; exact div_nonneg (by positivity) (by linarith))) hd
      _ ≤ gamma (l.length + 1) u := gamma_step hu hs

lemma sequential_expansion (term err : ℕ → ℝ) (L : ℕ) :
    sequentialSum term err L = ∑ p ∈ Finset.range L, term p * additionFactor err L p := by
  induction L using Nat.twoStepInduction with
  | zero => simp [sequentialSum]
  | one => simp [sequentialSum, additionFactor]
  | more k _ ih =>
    have hf (p : ℕ) (hp : p < k + 1) :
        additionFactor err (k + 2) p = additionFactor err (k + 1) p * (1 + err (k + 1)) := by
      unfold additionFactor
      exact Finset.prod_Ico_succ_top (by omega) _
    rw [sequentialSum, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    have hlast : additionFactor err (k + 2) (k + 1) = 1 + err (k + 1) := by
      simp [additionFactor, Nat.Ico_succ_singleton]
    rw [hlast, add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    rw [hf p (Finset.mem_range.mp hp)]
    ring

lemma slots_sum (f : ℕ → ℝ) (b T : ℕ) :
    (∑ r ∈ Finset.range b, ∑ t ∈ Finset.range T, f (r * T + t)) =
      ∑ j ∈ Finset.range (b * T), f j := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]

lemma coverage {n T : ℕ} (hT : 0 < T) : n ≤ blockCount n T * T := by
  have hmod := Nat.mod_lt (n + T - 1) hT
  have hdiv := Nat.div_add_mod (n + T - 1) T
  unfold blockCount
  nlinarith [show 1 ≤ T by omega, show n + T - 1 + 1 = n + T by omega]

lemma column_block {n T : ℕ} (hT : 0 < T) (j : Fin n) :
    j.val / T < blockCount n T := by
  apply (Nat.div_lt_iff_lt_mul hT).2
  exact lt_of_lt_of_le j.isLt (coverage hT)

lemma entryFactor_bound {m n : ℕ} (T : ℕ) (u : ℝ) (e : Roundoff m)
    (hT : 0 < T) (hu : 0 ≤ u) (hround : Admissible n T u e)
    (hs : (errorCount n T : ℝ) * u < 1) (i : Fin m) (j : Fin n) :
    |entryFactor n T e i j - 1| ≤ gamma (errorCount n T) u := by
  have hr := column_block hT j
  have ht := Nat.mod_lt j.val hT
  let l := e.mulError i (j.val / T) (j.val % T) ::
    ((Finset.Ico (max 1 (j.val % T)) T).toList.map (e.innerError i (j.val / T)) ++
     (Finset.Ico (max 1 (j.val / T)) (blockCount n T)).toList.map (e.outerError i))
  have hlen : l.length ≤ errorCount n T := by
    simp only [l, List.length_cons, List.length_append, List.length_map,
      Finset.length_toList, Nat.card_Ico]
    have hb : 1 ≤ blockCount n T := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hr)
    have hi : T - max 1 (j.val % T) ≤ T - 1 :=
      Nat.sub_le_sub_left (le_max_left 1 _) T
    have ho : blockCount n T - max 1 (j.val / T) ≤ blockCount n T - 1 :=
      Nat.sub_le_sub_left (le_max_left 1 _) _
    unfold errorCount
    omega
  have hl : ∀ d ∈ l, |d| ≤ u := by
    intro d hd
    simp only [l, List.mem_cons, List.mem_append, List.mem_map,
      Finset.mem_toList, Finset.mem_Ico] at hd
    rcases hd with hd | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · subst d
      exact hround.1 i _ _ hr ht
    · exact hround.2.1 i _ _ hr (by omega) hk.2
    · exact hround.2.2 i _ (by omega) hk.2
  have hprod : (l.map (fun d => 1 + d)).prod = entryFactor n T e i j := by
    simp [l, entryFactor, additionFactor, List.map_map, Finset.prod_map_toList, mul_assoc]
  rw [← hprod]
  apply (list_gamma l hu hl ?_).trans (gamma_mono hu hlen hs)
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hu) hs

lemma padded_sum {n : ℕ} (v x : Fin n → ℝ) (c : ℕ → ℝ) (N : ℕ) (hN : n ≤ N) :
    (∑ j ∈ Finset.range N, zeroPad v j * zeroPad x j * c j) =
      ∑ j : Fin n, v j * x j * c j.val := by
  rw [Finset.sum_fin_eq_sum_range]
  have heq : (∑ j ∈ Finset.range n, zeroPad v j * zeroPad x j * c j) =
      ∑ j ∈ Finset.range N, zeroPad v j * zeroPad x j * c j := by
    apply Finset.sum_subset (Finset.range_mono hN)
    intro j _ hj
    have hnj : ¬ j < n := by simpa using hj
    simp [zeroPad, hnj]
  rw [← heq]
  apply Finset.sum_congr rfl
  intro j hj
  simp [zeroPad, Finset.mem_range.mp hj]

lemma computed_expansion {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (T : ℕ) (e : Roundoff m) (hT : 0 < T) (i : Fin m) :
    computedVector A x T e i = ∑ j : Fin n, A i j * x j * entryFactor n T e i j := by
  let c : ℕ → ℝ := fun j => (1 + e.mulError i (j / T) (j % T)) *
    additionFactor (e.innerError i (j / T)) T (j % T) *
    additionFactor (e.outerError i) (blockCount n T) (j / T)
  calc
    computedVector A x T e i =
        ∑ r ∈ Finset.range (blockCount n T), ∑ t ∈ Finset.range T,
          zeroPad (A i) (r * T + t) * zeroPad x (r * T + t) * c (r * T + t) := by
      unfold computedVector
      rw [sequential_expansion]
      apply Finset.sum_congr rfl
      intro r hr
      rw [blockPartial, sequential_expansion, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t ht
      have ht' := Finset.mem_range.mp ht
      have hdiv : (r * T + t) / T = r := by
        rw [Nat.mul_comm r T, Nat.mul_add_div hT]
        simp [Nat.div_eq_of_lt ht']
      have hmod : (r * T + t) % T = t := by
        simp [Nat.add_mod, Nat.mod_eq_of_lt ht']
      simp only [roundedProduct, slotIndex, c, hdiv, hmod]
      ring
    _ = ∑ j ∈ Finset.range (blockCount n T * T), zeroPad (A i) j * zeroPad x j * c j :=
      slots_sum (fun j => zeroPad (A i) j * zeroPad x j * c j) (blockCount n T) T
    _ = ∑ j : Fin n, A i j * x j * entryFactor n T e i j := by
      exact padded_sum (A i) x c _ (coverage hT)

/-- Constructive form of the selected theorem, for the explicitly constructed
matrix perturbation. Only elementary operation errors are assumed bounded.
The proof follows the rounding factors of every original entry. -/
theorem constructed_backward_error
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (T : ℕ) (u : ℝ) (e : Roundoff m)
    (hT : 0 < T) (hu : 0 ≤ u)
    (hround : Admissible n T u e)
    (hsmall : (errorCount n T : ℝ) * u < 1) :
    computedVector A x T e = Matrix.mulVec (A + perturbation A T e) x ∧
      ∀ (i : Fin m) (j : Fin n),
        |perturbation A T e i j| ≤ gamma (errorCount n T) u * |A i j| := by
  constructor
  · funext i
    rw [computed_expansion A x T e hT i]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.add_apply, perturbation]
    ring
  · intro i j
    unfold perturbation
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (entryFactor_bound T u e hT hu hround hsmall i j)
      (abs_nonneg (A i j))).trans_eq (mul_comm _ _)

/-- The full source theorem: every admissible two-stage sequential execution
has a single entrywise bounded backward perturbation of the original matrix,
with the original vector unchanged and exactly `gamma_(T+ceil(n/T)-1)`. -/
theorem block_matrix_vector_product
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (T : ℕ) (u : ℝ) (e : Roundoff m)
    (hT : 0 < T) (hu : 0 ≤ u)
    (hround : Admissible n T u e)
    (hsmall : (errorCount n T : ℝ) * u < 1) :
    ∃ ΔA : Matrix (Fin m) (Fin n) ℝ,
      computedVector A x T e = Matrix.mulVec (A + ΔA) x ∧
        ∀ (i : Fin m) (j : Fin n),
          |ΔA i j| ≤ gamma (errorCount n T) u * |A i j| := by
  exact ⟨perturbation A T e,
    constructed_backward_error A x T u e hT hu hround hsmall⟩

end BlockMatrixVector
