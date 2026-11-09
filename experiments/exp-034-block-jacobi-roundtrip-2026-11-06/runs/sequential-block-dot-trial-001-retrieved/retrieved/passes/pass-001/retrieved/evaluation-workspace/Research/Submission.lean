import Mathlib

/-!
Formal statement of `corollary:block_dot_product_sequential` in source.txt.
The elementary relative-error model encodes the no-overflow/no-underflow
assumption. All errors are local operation errors; no global expansion or
algorithmic error estimate is assumed.
-/

namespace BlockDotProduct

/-- Number of blocks, i.e. `ceil (n / T)` for positive `T`. -/
def blockCount (n T : ℕ) : ℕ := (n + T - 1) / T

/-- The depth `ceil (log₂ B)` of the binary-tree algorithm in the inherited
assumptions. `Nat.clog` is the natural-number ceiling logarithm. -/
def treeDepth (B : ℕ) : ℕ := Nat.clog 2 B

/-- Deterministic rounding-error constant. Its use requires `m * u < 1`. -/
noncomputable def gamma (m : ℕ) (u : ℝ) : ℝ :=
  (m : ℝ) * u / (1 - (m : ℝ) * u)

/-- Extend an original vector by zero, including all padding in the last block. -/
def zeroExtend {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then x ⟨i, h⟩ else 0

/-- An admissible operation-indexed execution in the standard relative-rounding
model. `productError b t` belongs to multiplication at offset `t` of block `b`;
`blockAddError b t` belongs to inserting offset `t` (only `t ≥ 1` is used);
`reductionError b` belongs to inserting partial `b` (only `b ≥ 1` is used).
Errors on unused indices have no effect. Independent errors allow every
execution of an actual rounding operation satisfying the model. -/
structure RoundingTrace (u : ℝ) where
  productError : ℕ → ℕ → ℝ
  blockAddError : ℕ → ℕ → ℝ
  reductionError : ℕ → ℝ
  productError_bound : ∀ b t, |productError b t| ≤ u
  blockAddError_bound : ∀ b t, |blockAddError b t| ≤ u
  reductionError_bound : ∀ b, |reductionError b| ≤ u

/-- Sequential summation of exactly `L` entries: initialize with entry zero,
then perform `L - 1` rounded additions. The empty case is defined for totality.
In particular there is no rounded addition to zero on initialization. -/
def sequentialSum (entry error : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => if k = 0 then entry 0
      else (sequentialSum entry error k + entry k) * (1 + error k)

/-- Each padded or original product receives its own multiplication rounding. -/
def roundedProduct {n : ℕ} {u : ℝ} (x y : Fin n → ℝ)
    (trace : RoundingTrace u) (T b t : ℕ) : ℝ :=
  (zeroExtend x (b * T + t) * zeroExtend y (b * T + t)) *
    (1 + trace.productError b t)

/-- A sequential dot product of exactly `T` entries of block `b`. -/
def blockPartial {n : ℕ} {u : ℝ} (x y : Fin n → ℝ)
    (T : ℕ) (trace : RoundingTrace u) (b : ℕ) : ℝ :=
  sequentialSum (roundedProduct x y trace T b) (trace.blockAddError b) T

/-- The computed scalar: sequential reduction of the actual rounded block
partials of the original, zero-padded vectors. -/
def sequentialBlockDotProduct {n : ℕ} {u : ℝ} (x y : Fin n → ℝ)
    (T : ℕ) (trace : RoundingTrace u) : ℝ :=
  sequentialSum (blockPartial x y T trace) trace.reductionError (blockCount n T)

/-- Errors on the addition path of an entry. -/
def sumPath (error : ℕ → ℝ) : ℕ → ℕ → List ℝ
  | 0, _ => []
  | k + 1, i => if k = 0 then [] else
      if i < k then sumPath error k i ++ [error k] else [error k]

lemma sumPath_length (e : ℕ → ℝ) (L i : ℕ) :
    (sumPath e L i).length ≤ L - 1 := by
  induction L with
  | zero => simp [sumPath]
  | succ k ih =>
    simp only [sumPath]
    split_ifs with hk hi
    · simp
    · simpa using (show (sumPath e k i).length + 1 ≤ k by
        have := ih
        omega)
    · simp; omega

lemma sumPath_mem (e : ℕ → ℝ) (u : ℝ) (he : ∀ i, |e i| ≤ u)
    (L i : ℕ) : ∀ d ∈ sumPath e L i, |d| ≤ u := by
  induction L with
  | zero => simp [sumPath]
  | succ k ih =>
    simp only [sumPath]
    split_ifs with hk hi
    · simp
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact ih d hd
      · have : d = e k := by simpa using hd
        simpa [this] using he k
    · intro d hd
      have : d = e k := by simpa using hd
      simpa [this] using he k

lemma sequential_expansion (a e : ℕ → ℝ) (L : ℕ) :
    sequentialSum a e L = ∑ i ∈ Finset.range L,
      a i * ((sumPath e L i).map (fun d => 1 + d)).prod := by
  induction L with
  | zero => simp [sequentialSum]
  | succ k ih =>
    by_cases hk : k = 0
    · subst k; simp [sequentialSum, sumPath]
    · rw [sequentialSum, if_neg hk, ih, Finset.sum_range_succ]
      simp only [sumPath, if_neg hk, lt_self_iff_false, ↓reduceIte,
        List.map_singleton, List.prod_singleton]
      rw [add_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi, List.map_append, List.prod_append, mul_assoc]

lemma error_product_bound (u : ℝ) (hu : 0 ≤ u) (l : List ℝ)
    (he : ∀ d ∈ l, |d| ≤ u)
    (hs : (l.length : ℝ) * u < 1) :
    |(l.map (fun d => 1 + d)).prod - 1| ≤ gamma l.length u := by
  induction l with
  | nil => simp [gamma]
  | cons d l ih =>
    have hd := he d (by simp)
    have hl : (l.length : ℝ) * u < 1 := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hs
      nlinarith
    have hb := ih (fun d hd => he d (by simp [hd])) hl
    have hp : 0 < 1 - (l.length : ℝ) * u := by linarith
    have hq : 0 < 1 - ((l.length : ℝ) + 1) * u := by
      simpa using sub_pos.mpr hs
    have hbn : 0 ≤ gamma l.length u := div_nonneg (mul_nonneg (by positivity) hu) (le_of_lt hp)
    have htri : |(1 + d) * (l.map (fun d => 1 + d)).prod - 1| ≤
        gamma l.length u * (1 + u) + u := by
      calc
        _ = |((l.map (fun d => 1 + d)).prod - 1) * (1 + d) + d| := by congr 1; ring
        _ ≤ |(l.map (fun d => 1 + d)).prod - 1| * |1 + d| + |d| := by
          simpa only [abs_mul] using abs_add_le (((l.map (fun d => 1 + d)).prod - 1) * (1 + d)) d
        _ ≤ gamma l.length u * (1 + u) + u := by
          have hd1 : |1 + d| ≤ 1 + u := (abs_add_le 1 d).trans (by simpa using hd)
          exact add_le_add (mul_le_mul hb hd1 (abs_nonneg _) hbn) hd
    simp only [List.map_cons, List.prod_cons]
    refine htri.trans ?_
    simp only [gamma, List.length_cons, Nat.cast_add, Nat.cast_one]
    apply (le_div_iff₀ hq).2
    field_simp
    nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ l.length by positivity) hu) hu]

lemma error_product_bound_budget (u : ℝ) (hu : 0 ≤ u) (l : List ℝ)
    (he : ∀ d ∈ l, |d| ≤ u) (M : ℕ) (hm : l.length ≤ M)
    (hs : (M : ℝ) * u < 1) :
    |(l.map (fun d => 1 + d)).prod - 1| ≤ gamma M u := by
  have hm' : (l.length : ℝ) * u ≤ (M : ℝ) * u :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hu
  refine (error_product_bound u hu l he (lt_of_le_of_lt hm' hs)).trans ?_
  unfold gamma
  apply (div_le_div_iff₀ (by linarith : 0 < 1 - (l.length : ℝ)*u) (by linarith : 0 < 1 - (M:ℝ)*u)).2
  nlinarith

def fullPath {u : ℝ} (trace : RoundingTrace u) (T B b t : ℕ) : List ℝ :=
  trace.productError b t :: (sumPath (trace.blockAddError b) T t ++
    sumPath trace.reductionError B b)

lemma fullPath_bound {u : ℝ} (hu : 0 ≤ u) (trace : RoundingTrace u)
    (T B : ℕ) (hT : 0 < T) (hB : 0 < B)
    (hs : ((T + B - 1 : ℕ) : ℝ) * u < 1) (b t : ℕ) :
    |((fullPath trace T B b t).map (fun d => 1 + d)).prod - 1| ≤
      gamma (T + B - 1) u := by
  apply error_product_bound_budget u hu
  · intro d hd
    simp only [fullPath, List.mem_cons, List.mem_append] at hd
    rcases hd with hd | hd | hd
    · subst d; exact trace.productError_bound b t
    · exact sumPath_mem _ u (trace.blockAddError_bound b) T t d hd
    · exact sumPath_mem _ u trace.reductionError_bound B b d hd
  · simp only [fullPath, List.length_cons, List.length_append]
    have := sumPath_length (trace.blockAddError b) T t
    have := sumPath_length trace.reductionError B b
    omega
  · exact hs

lemma rectangular_sum (B T : ℕ) (hT : 0 < T) (f : ℕ → ℕ → ℝ) :
    (∑ b ∈ Finset.range B, ∑ t ∈ Finset.range T, f b t) =
      ∑ i ∈ Finset.range (B*T), f (i/T) (i%T) := by
  rw [← Finset.sum_product (Finset.range B) (Finset.range T) (fun p => f p.1 p.2)]
  apply Finset.sum_bij (fun p _ => p.1*T+p.2)
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
    calc
      p.1*T+p.2 < p.1*T+T := Nat.add_lt_add_left hp.2 _
      _ = (p.1+1)*T := by ring
      _ ≤ B*T := Nat.mul_le_mul_right T hp.1
  · intro p hp q hq heq
    simp only [Finset.mem_product, Finset.mem_range] at hp hq
    have hpd : (p.1*T+p.2)/T = p.1 := by simp [Nat.mul_comm p.1 T, Nat.mul_add_div hT, Nat.div_eq_of_lt hp.2]
    have hqd : (q.1*T+q.2)/T = q.1 := by simp [Nat.mul_comm q.1 T, Nat.mul_add_div hT, Nat.div_eq_of_lt hq.2]
    have h1 : p.1 = q.1 := by rw [← hpd, ← hqd, heq]
    apply Prod.ext h1
    rw [h1] at heq
    exact Nat.add_left_cancel heq
  · intro i hi
    refine ⟨(i/T, i%T), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range] at hi ⊢
      exact ⟨(Nat.div_lt_iff_lt_mul hT).2 hi, Nat.mod_lt _ hT⟩
    · simpa [Nat.mul_comm] using Nat.div_add_mod i T
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    simp [Nat.mul_comm p.1 T, Nat.mul_add_div hT, Nat.div_eq_of_lt hp.2,
      Nat.mod_eq_of_lt hp.2]

lemma blockCount_cover (n T : ℕ) (hT : 0 < T) : n ≤ blockCount n T * T := by
  have h := Nat.mod_lt (n+T-1) hT
  have he := Nat.mod_add_div (n+T-1) T
  unfold blockCount
  have he' : (n+T-1) % T + ((n+T-1)/T)*T = n+T-1 := by
    simpa [Nat.mul_comm] using he
  omega

lemma padded_sum {n : ℕ} (x y : Fin n → ℝ) (N : ℕ) (hN : n ≤ N)
    (c : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, (zeroExtend x i * zeroExtend y i) * c i) =
      ∑ i : Fin n, (x i * y i) * c i := by
  calc
    _ = ∑ i ∈ Finset.range n, (zeroExtend x i * zeroExtend y i) * c i := by
      symm
      apply Finset.sum_subset (Finset.range_mono hN)
      intro i hi hn
      have hn' : ¬i < n := by simpa using hn
      simp [zeroExtend, hn']
    _ = _ := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp [zeroExtend, i.isLt]

lemma algorithm_expansion {n : ℕ} {u : ℝ} (x y : Fin n → ℝ)
    (T : ℕ) (hT : 0 < T) (trace : RoundingTrace u) :
    sequentialBlockDotProduct x y T trace =
      ∑ i : Fin n, (x i * y i) *
        ((fullPath trace T (blockCount n T) (i.val/T) (i.val%T)).map
          (fun d => 1 + d)).prod := by
  unfold sequentialBlockDotProduct
  rw [sequential_expansion]
  simp only [blockPartial, sequential_expansion, Finset.sum_mul]
  have he : (∑ b ∈ Finset.range (blockCount n T),
      ∑ t ∈ Finset.range T,
      roundedProduct x y trace T b t *
        ((sumPath (trace.blockAddError b) T t).map (fun d => 1+d)).prod *
        ((sumPath trace.reductionError (blockCount n T) b).map (fun d => 1+d)).prod) =
      ∑ b ∈ Finset.range (blockCount n T), ∑ t ∈ Finset.range T,
        (zeroExtend x (b*T+t) * zeroExtend y (b*T+t)) *
        ((fullPath trace T (blockCount n T) b t).map (fun d => 1+d)).prod := by
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro t ht
    simp [roundedProduct, fullPath, List.map_append, List.prod_append, mul_assoc]
  rw [he, rectangular_sum _ _ hT]
  simp only [Nat.mul_comm (_ / T) T, Nat.div_add_mod]
  exact padded_sum x y _ (blockCount_cover n T hT) _

/-- Sequential Reduction of the Partial Dot Products.

The input dimension and block size are positive. In addition to the selected
sequential condition, `h_tree` explicitly retains the small-roundoff condition
from the referenced block-dot-product theorem. Both representations refer to
the same computed scalar and to the original unpadded vectors. The hypotheses
contain only dimension conditions and the elementary relative-rounding model.
-/
theorem block_dot_product_sequential
    (n T : ℕ) (hn : 0 < n) (hT : 0 < T)
    (u : ℝ) (hu : 0 ≤ u)
    (x y : Fin n → ℝ) (trace : RoundingTrace u)
    (h_tree : ((T + treeDepth (blockCount n T) : ℕ) : ℝ) * u < 1)
    (h_sequential : ((T + blockCount n T - 1 : ℕ) : ℝ) * u < 1) :
    ∃ (Δx Δy : Fin n → ℝ),
      (sequentialBlockDotProduct x y T trace =
        ∑ i : Fin n, (x i + Δx i) * y i) ∧
      (∀ i : Fin n, |Δx i| ≤ gamma (T + blockCount n T - 1) u * |x i|) ∧
      (sequentialBlockDotProduct x y T trace =
        ∑ i : Fin n, x i * (y i + Δy i)) ∧
      (∀ i : Fin n, |Δy i| ≤ gamma (T + blockCount n T - 1) u * |y i|) := by
  have hcover := blockCount_cover n T hT
  have hB : 0 < blockCount n T := by
    by_contra h
    have : blockCount n T = 0 := by omega
    simp [this] at hcover
    omega
  let c : Fin n → ℝ := fun i =>
    ((fullPath trace T (blockCount n T) (i.val/T) (i.val%T)).map
      (fun d => 1+d)).prod
  have hc (i : Fin n) : |c i - 1| ≤ gamma (T + blockCount n T - 1) u :=
    fullPath_bound hu trace T (blockCount n T) hT hB h_sequential _ _
  have hexp : sequentialBlockDotProduct x y T trace =
      ∑ i : Fin n, (x i * y i) * c i := algorithm_expansion x y T hT trace
  refine ⟨(fun i => (c i - 1) * x i), (fun i => (c i - 1) * y i), ?_, ?_, ?_, ?_⟩
  · rw [hexp]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro i
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hc i) (abs_nonneg _)
  · rw [hexp]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro i
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hc i) (abs_nonneg _)

end BlockDotProduct
