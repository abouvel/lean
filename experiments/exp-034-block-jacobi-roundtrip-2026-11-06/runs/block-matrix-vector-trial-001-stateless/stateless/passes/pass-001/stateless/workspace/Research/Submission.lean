import Mathlib

/-!
Formalization of /spec/source.txt, theorem:block_matrix_vector_product.

The rounding trace records relative errors for individual multiplications and
additions. Its validity is exactly the standard relative-error model on the
operations executed here, the mathematical consequence of no overflow/underflow.
Errors may depend arbitrarily on the inputs and on earlier operations.

Statement revision record: initial statement; /spec/feedback.json was absent.
No supporting source files were supplied in /spec/support. The positive block
size and nonnegative unit roundoff make the source's implicit domains explicit.
Empty dot products are zero; no positivity of either matrix dimension is assumed.
-/

namespace BlockMatrixVector

/-- Number of blocks, equal to `ceil(n / T)` for a positive block size. -/
def blockCount (n T : ℕ) : ℕ := (n + T - 1) / T

/-- Maximum number of rounding factors along a term's computation path. -/
def errorCount (n T : ℕ) : ℕ := T + blockCount n T - 1

/-- The source's deterministic error constant. -/
noncomputable def gamma (k : ℕ) (u : ℝ) : ℝ := (k : ℝ) * u / (1 - (k : ℝ) * u)

/-- Extend a vector by zero beyond its original dimension. -/
def padded {n : ℕ} (v : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then v ⟨j, h⟩ else 0

/-- Sequential summation of `v 0, ..., v (k-1)`. The first term is copied,
not added to a zero accumulator; `δ s` is used when term `s ≥ 1` is added. -/
def sequentialSum (v δ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => if k = 0 then v 0
      else (sequentialSum v δ k + v k) * (1 + δ k)

/-- A separate local error for every executed operation of every row.
Natural indices avoid artificial restrictions on traces outside the execution. -/
structure RoundingTrace (m : ℕ) where
  mulError : Fin m → ℕ → ℕ → ℝ
  blockAddError : Fin m → ℕ → ℕ → ℝ
  outerAddError : Fin m → ℕ → ℝ

/-- Operation-level rounding assumptions. In particular, this predicate assumes
no error bound for a whole dot product or matrix-vector product. -/
def RoundingTrace.Valid {m : ℕ} (E : RoundingTrace m) (n T : ℕ) (u : ℝ) : Prop :=
  (∀ (i : Fin m) (b : ℕ), b < blockCount n T →
    ∀ (t : ℕ), t < T → |E.mulError i b t| ≤ u) ∧
  (∀ (i : Fin m) (b : ℕ), b < blockCount n T →
    ∀ (t : ℕ), 1 ≤ t → t < T → |E.blockAddError i b t| ≤ u) ∧
  (∀ (i : Fin m) (b : ℕ), 1 ≤ b → b < blockCount n T →
    |E.outerAddError i b| ≤ u)

/-- A rounded multiplication, including products of zero-padded operands. -/
def roundedProduct {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (T : ℕ) (E : RoundingTrace m)
    (i : Fin m) (b t : ℕ) : ℝ :=
  (padded (A i) (b * T + t) * padded x (b * T + t)) *
    (1 + E.mulError i b t)

/-- A block dot product uses `T` multiplications and `T-1` additions for `T>0`. -/
def blockPartial {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (T : ℕ) (E : RoundingTrace m)
    (i : Fin m) (b : ℕ) : ℝ :=
  sequentialSum (roundedProduct A x T E i b) (E.blockAddError i b) T

/-- The actual computed vector: sequential dot products within blocks,
followed by sequential reduction of the block partial sums in each row. -/
def computed {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (T : ℕ) (E : RoundingTrace m) : Fin m → ℝ :=
  fun i => sequentialSum (blockPartial A x T E i) (E.outerAddError i)
    (blockCount n T)

/-- Multiplicative coefficient on original column `j` along its rounding path.
For zero-based term `t`, additions begin at `max 1 t`. This includes the first
addition for both initial terms and handles `T=1` without a special formula. -/
noncomputable def pathCoefficient {m n : ℕ} (T : ℕ) (E : RoundingTrace m)
    (i : Fin m) (j : Fin n) : ℝ :=
  let b := j.val / T
  let t := j.val % T
  (1 + E.mulError i b t) *
    (∏ s ∈ Finset.Ico (max 1 t) T, (1 + E.blockAddError i b s)) *
    (∏ s ∈ Finset.Ico (max 1 b) (blockCount n T), (1 + E.outerAddError i s))

/-- Explicit backward perturbation; it never divides by an input entry. -/
noncomputable def perturbation {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (T : ℕ) (E : RoundingTrace m) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => A i j * (pathCoefficient T E i j - 1)

lemma sequentialSum_expansion (v δ : ℕ → ℝ) (k : ℕ) :
    sequentialSum v δ k = ∑ t ∈ Finset.range k,
      v t * ∏ s ∈ Finset.Ico (max 1 t) k, (1 + δ s) := by
  induction k with
  | zero => simp [sequentialSum]
  | succ k ih =>
    by_cases hk : k = 0
    · subst k; simp [sequentialSum]
    · have hk1 : 1 ≤ k := by omega
      rw [sequentialSum, if_neg hk, ih, add_mul, Finset.sum_mul,
        Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.prod_Ico_succ_top (by
          have := Finset.mem_range.mp ht
          omega)]
        ring
      · simp [max_eq_right hk1]

lemma list_error_bound (l : List ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hl : ∀ d ∈ l, |d| ≤ u) (hs : (l.length : ℝ) * u < 1) :
    |(l.map (fun d => 1 + d)).prod - 1| ≤
      (l.length : ℝ) * u / (1 - (l.length : ℝ) * u) := by
  induction l with
  | nil => simp
  | cons d l ih =>
    have hd := hl d (by simp)
    have hl' : ∀ e ∈ l, |e| ≤ u := fun e he => hl e (by simp [he])
    have hlen : (0 : ℝ) ≤ l.length := Nat.cast_nonneg _
    have hs' : (l.length : ℝ) * u < 1 := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hs
      nlinarith
    have hb := ih hl' hs'
    have hp : 0 < 1 - (l.length : ℝ) * u := by linarith
    have hp' : 0 < 1 - ((l.length : ℝ) + 1) * u := by
      simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using sub_pos.mpr hs
    let z := (l.map (fun d => 1 + d)).prod - 1
    have hz : |z| * (1 - (l.length : ℝ) * u) ≤ (l.length : ℝ) * u :=
      (le_div_iff₀ hp).mp hb
    have he : |(1 + d) * (l.map (fun d => 1 + d)).prod - 1| ≤
        |z| * (1 + u) + u := by
      have hid : (1 + d) * (l.map (fun d => 1 + d)).prod - 1 = z + d*z + d := by
        dsimp [z]; ring
      rw [hid]
      calc
        |z + d*z + d| ≤ |z| + |d*z| + |d| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ |z| + u * |z| + u := by
          rw [abs_mul]
          gcongr
        _ = |z| * (1 + u) + u := by ring
    simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    apply (le_div_iff₀ hp').mpr
    have hz0 := abs_nonneg z
    have hh : 0 ≤ (l.length : ℝ) * u := mul_nonneg hlen hu
    have haux : (|z| * (1 + u) + u) *
        (1 - ((l.length : ℝ) + 1) * u) ≤ ((l.length : ℝ) + 1) * u := by
      nlinarith [mul_nonneg hh (sq_nonneg u), mul_nonneg (mul_nonneg hz0 hh) (sq_nonneg u)]
    exact (mul_le_mul_of_nonneg_right he hp'.le).trans haux

lemma list_error_bound_mono (l : List ℝ) (K : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hl : ∀ d ∈ l, |d| ≤ u) (hlen : l.length ≤ K)
    (hs : (K : ℝ) * u < 1) :
    |(l.map (fun d => 1 + d)).prod - 1| ≤ gamma K u := by
  have hle : (l.length : ℝ) * u ≤ (K : ℝ) * u :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hu
  have hp : 0 < 1 - (K : ℝ) * u := by linarith
  have hp' : 0 < 1 - (l.length : ℝ) * u := by linarith
  apply (list_error_bound l u hu hl (hle.trans_lt hs)).trans
  unfold gamma
  apply (div_le_div_iff₀ hp' hp).mpr
  nlinarith

lemma block_coverage (n T : ℕ) (hT : 0 < T) : n ≤ blockCount n T * T := by
  have h := Nat.mod_lt (n + T - 1) hT
  have he := Nat.mod_add_div (n + T - 1) T
  unfold blockCount
  rw [Nat.mul_comm] at he
  omega

lemma sum_blocks (f : ℕ → ℝ) (B T : ℕ) (hT : 0 < T) :
    (∑ b ∈ Finset.range B, ∑ t ∈ Finset.range T, f (b*T+t)) =
      ∑ j ∈ Finset.range (B*T), f j := by
  rw [← Finset.sum_product' (Finset.range B) (Finset.range T) (fun b t => f (b*T+t))]
  apply Finset.sum_bij (fun p _ => p.1*T+p.2)
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
    nlinarith [hp.1, hp.2]
  · intro p hp q hq he
    simp only [Finset.mem_product, Finset.mem_range] at hp hq
    have hd := congrArg (fun z => z / T) he
    have hm := congrArg (fun z => z % T) he
    have hd' : p.1 = q.1 := by
      simpa only [Nat.mul_comm _ T, Nat.mul_add_div hT, Nat.div_eq_of_lt hp.2,
        Nat.div_eq_of_lt hq.2, Nat.add_zero] using hd
    have hm' : p.2 = q.2 := by
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hp.2, Nat.mod_eq_of_lt hq.2] using hm
    exact Prod.ext hd' hm' 
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    have hb : j / T < B := (Nat.div_lt_iff_lt_mul hT).mpr hj'
    refine ⟨(j/T,j%T), ?_, ?_⟩
    · simp [hb, Nat.mod_lt j hT]
    · dsimp; simpa [Nat.mul_comm] using Nat.div_add_mod j T
  · intro p hp; rfl

lemma pathCoefficient_bound {m n T : ℕ} (E : RoundingTrace m)
    (u : ℝ) (hT : 0 < T) (hu : 0 ≤ u) (hm : E.Valid n T u)
    (hs : (errorCount n T : ℝ) * u < 1) (i : Fin m) (j : Fin n) :
    |pathCoefficient T E i j - 1| ≤ gamma (errorCount n T) u := by
  let b := j.val / T
  let t := j.val % T
  have ht : t < T := Nat.mod_lt _ hT
  have hb : b < blockCount n T := (Nat.div_lt_iff_lt_mul hT).mpr
    (lt_of_lt_of_le j.isLt (block_coverage n T hT))
  let l := [E.mulError i b t] ++
    ((Finset.Ico (max 1 t) T).toList.map (E.blockAddError i b)) ++
    ((Finset.Ico (max 1 b) (blockCount n T)).toList.map (E.outerAddError i))
  have hl : ∀ d ∈ l, |d| ≤ u := by
    intro d hd
    simp only [l, List.mem_append, List.mem_singleton, List.mem_map,
      Finset.mem_toList, Finset.mem_Ico] at hd
    rcases hd with (rfl | ⟨s, ⟨hs1, hs2⟩, rfl⟩) | ⟨s, ⟨hs1, hs2⟩, rfl⟩
    · exact hm.1 i b hb t ht
    · exact hm.2.1 i b hb s (by omega) hs2
    · exact hm.2.2 i s (by omega) hs2
  have hlen : l.length ≤ errorCount n T := by
    simp only [l, List.length_append, List.length_singleton, List.length_map,
      Finset.length_toList, Nat.card_Ico]
    unfold errorCount
    have h1 : 1 ≤ max 1 t := le_max_left _ _
    have h2 : 1 ≤ max 1 b := le_max_left _ _
    have hB : 0 < blockCount n T := lt_of_le_of_lt (Nat.zero_le b) hb
    calc
      1 + (T - max 1 t) + (blockCount n T - max 1 b) ≤
          1 + (T - 1) + (blockCount n T - 1) := by omega
      _ = T + blockCount n T - 1 := by omega
  have he : (l.map (fun d => 1+d)).prod = pathCoefficient T E i j := by
    simp [l, List.map_append, List.prod_append, List.map_map,
      Finset.prod_map_toList, pathCoefficient, b, t, mul_assoc]
  rw [← he]
  exact list_error_bound_mono l (errorCount n T) u hu hl hlen hs

lemma computed_expansion {m n T : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (E : RoundingTrace m) (hT : 0 < T) (i : Fin m) :
    computed A x T E i = ∑ j : Fin n, A i j * x j * pathCoefficient T E i j := by
  let c : ℕ → ℝ := fun j =>
    (1 + E.mulError i (j/T) (j%T)) *
    (∏ s ∈ Finset.Ico (max 1 (j%T)) T, (1 + E.blockAddError i (j/T) s)) *
    (∏ s ∈ Finset.Ico (max 1 (j/T)) (blockCount n T), (1 + E.outerAddError i s))
  let f : ℕ → ℝ := fun j => padded (A i) j * padded x j * c j
  have hflat : computed A x T E i =
      ∑ b ∈ Finset.range (blockCount n T), ∑ t ∈ Finset.range T, f (b*T+t) := by
    unfold computed
    rw [sequentialSum_expansion]
    apply Finset.sum_congr rfl
    intro b hb
    unfold blockPartial
    rw [sequentialSum_expansion, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    have ht' := Finset.mem_range.mp ht
    have hd : (b*T+t)/T = b := by
      rw [Nat.mul_comm b T, Nat.mul_add_div hT, Nat.div_eq_of_lt ht', Nat.add_zero]
    have hm : (b*T+t)%T = t := by simp [Nat.add_mod, Nat.mod_eq_of_lt ht']
    dsimp [f, c, roundedProduct]
    rw [hd, hm]
    ring
  rw [hflat, sum_blocks f (blockCount n T) T hT]
  have hsum : (∑ j ∈ Finset.range n, f j) =
      ∑ j ∈ Finset.range (blockCount n T*T), f j := by
    apply Finset.sum_subset
    · exact Finset.range_mono (block_coverage n T hT)
    · intro j hj hjn
      have hn : ¬ j < n := by simpa using hjn
      simp [f, padded, hn]
  rw [← hsum, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  simp [f, padded, hj', c, pathCoefficient]

/-- The source theorem with the explicit perturbation constructed from the
actual computation. All assumptions are local rounding bounds or the source's
smallness condition; the vector input is unchanged. -/
theorem block_matrix_vector_product_constructed
    {m n T : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (u : ℝ) (E : RoundingTrace m)
    (hT : 0 < T) (hu : 0 ≤ u) (hmodel : E.Valid n T u)
    (hsmall : (errorCount n T : ℝ) * u < 1) :
    computed A x T E = (A + perturbation A T E).mulVec x ∧
      ∀ (i : Fin m) (j : Fin n),
        |perturbation A T E i j| ≤ gamma (errorCount n T) u * |A i j| := by
  constructor
  · funext i
    rw [computed_expansion A x E hT i]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Matrix.add_apply, perturbation]
    ring
  · intro i j
    unfold perturbation
    rw [abs_mul, mul_comm (gamma (errorCount n T) u)]
    exact mul_le_mul_of_nonneg_left
      (pathCoefficient_bound E u hT hu hmodel hsmall i j) (abs_nonneg _)

/-- Block Matrix-vector Product (theorem:block_matrix_vector_product):
existence of a componentwise bounded matrix backward error for the defined
sequential blocked execution, with precisely `γ_(T+ceil(n/T)-1)`. -/
theorem block_matrix_vector_product
    {m n T : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (u : ℝ) (E : RoundingTrace m)
    (hT : 0 < T) (hu : 0 ≤ u) (hmodel : E.Valid n T u)
    (hsmall : (errorCount n T : ℝ) * u < 1) :
    ∃ ΔA : Matrix (Fin m) (Fin n) ℝ,
      computed A x T E = (A + ΔA).mulVec x ∧
      ∀ (i : Fin m) (j : Fin n),
        |ΔA i j| ≤ gamma (errorCount n T) u * |A i j| := by
  exact ⟨perturbation A T E,
    block_matrix_vector_product_constructed A x u E hT hu hmodel hsmall⟩

end BlockMatrixVector
