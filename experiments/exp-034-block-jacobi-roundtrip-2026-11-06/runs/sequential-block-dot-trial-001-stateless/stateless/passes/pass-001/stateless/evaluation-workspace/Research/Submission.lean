import Mathlib

/-!
Formalization of Sahil Bhola, `corollary:block_dot_product_sequential`.
Indices are zero based; vectors have exactly `n` entries. `T > 0` is explicit.
We also allow `n = 0`, with empty execution equal to zero.

The standard floating-point model, including the exclusion of overflow and
underflow, is represented by an admissible operation-indexed relative-error
trace. Every executed product/addition below has precisely the value
`(exact operation) * (1 + δ)` with `|δ| ≤ u`. No conclusion about the
algorithm's error is included in admissibility. Unused trace entries are
unrestricted. The real arithmetic specifies the rounding model rather than
an implementation-specific floating-point format.

No feedback.json was supplied. Statement revisions: none relative to an
existing Lean statement (the initial file contained only `import Mathlib`).
The fallible plan is made explicit by retaining its inherited binary-tree
smallness assumption, while replacing the tree execution by sequential
reduction. The empty-input convention extends the usual nonempty case.
-/

namespace Research.BlockDotProduct

noncomputable section

/-- Number of blocks: ceiling division for positive `T`. -/
def blockCount (n T : ℕ) : ℕ := (n + T - 1) / T

/-- The inherited binary-tree depth `⌈log₂ (⌈n/T⌉)⌉`. -/
def treeDepth (n T : ℕ) : ℕ := Nat.clog 2 (blockCount n T)

/-- The precise sequential-reduction error index, with natural subtraction. -/
def errorIndex (n T : ℕ) : ℕ := T + blockCount n T - 1

/-- Higham's deterministic error constant. Its use requires `k*u < 1`. -/
def gamma (k : ℕ) (u : ℝ) : ℝ := (k : ℝ) * u / (1 - (k : ℝ) * u)

/-- Extend an original vector by zeros, including the last incomplete block. -/
def padded {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then x ⟨i, h⟩ else 0

/-- Relative errors for the individual operations; slot zero of each addition
trace is unused because accumulation starts with the first term. -/
structure RoundingTrace where
  mulError : ℕ → ℕ → ℝ
  blockAddError : ℕ → ℕ → ℝ
  reductionAddError : ℕ → ℝ

/-- Exactly the common rounding-model bounds on the operations executed by
this algorithm. This is the numerical no-exception model, with no bound on
input signs or magnitudes and no algorithmic error estimate as a premise. -/
def RoundingTrace.Admissible (e : RoundingTrace) (n T : ℕ) (u : ℝ) : Prop :=
  (∀ j < blockCount n T, ∀ t < T, |e.mulError j t| ≤ u) ∧
  (∀ j < blockCount n T, ∀ t, 0 < t → t < T → |e.blockAddError j t| ≤ u) ∧
  (∀ j, 0 < j → j < blockCount n T → |e.reductionAddError j| ≤ u)

/-- Rounded sequential summation of `count` terms. It uses `count - 1`
additions for a nonempty input; the first term is copied without rounding. -/
def sequentialSum (a δ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => if k = 0 then a 0
      else (sequentialSum a δ k + a k) * (1 + δ k)

/-- A rounded multiplication in block `j`, slot `t`. -/
def roundedProduct {n : ℕ} (T : ℕ) (x y : Fin n → ℝ)
    (e : RoundingTrace) (j t : ℕ) : ℝ :=
  (padded x (j * T + t) * padded y (j * T + t)) * (1 + e.mulError j t)

/-- Each block computes all `T` products and then sequentially adds them. -/
def blockPartial {n : ℕ} (T : ℕ) (x y : Fin n → ℝ)
    (e : RoundingTrace) (j : ℕ) : ℝ :=
  sequentialSum (roundedProduct T x y e j) (e.blockAddError j) T

/-- The actual computed result: sequential reduction of the computed partials. -/
def computedDot {n : ℕ} (T : ℕ) (x y : Fin n → ℝ) (e : RoundingTrace) : ℝ :=
  sequentialSum (blockPartial T x y e) e.reductionAddError (blockCount n T)

/-- Multipliers affecting term `i` in a sequential sum. For term zero the
first rounding is addition 1; for any later term it is the addition inserting
that term. Empty products cover singleton sums. -/
def sequentialWeight (δ : ℕ → ℝ) (count i : ℕ) : ℝ :=
  ∏ k ∈ Finset.Ico (max 1 i) count, (1 + δ k)

/-- The explicit coefficient of original term `i`: its product error, its
within-block addition factors, and its outer-reduction addition factors. -/
def termCoefficient (n T : ℕ) (e : RoundingTrace) (i : Fin n) : ℝ :=
  (1 + e.mulError (i.val / T) (i.val % T)) *
    sequentialWeight (e.blockAddError (i.val / T)) T (i.val % T) *
    sequentialWeight e.reductionAddError (blockCount n T) (i.val / T)

/-- Componentwise perturbation; no division by input components is required. -/
def backwardPerturbation {n : ℕ} (T : ℕ) (e : RoundingTrace)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (termCoefficient n T e i - 1) * x i

lemma sequential_expansion (a δ : ℕ → ℝ) (m : ℕ) :
    sequentialSum a δ m =
      ∑ i ∈ Finset.range m, a i * sequentialWeight δ m i := by
  induction m with
  | zero => simp [sequentialSum]
  | succ m ih =>
    by_cases hm : m = 0
    · subst m
      simp [sequentialSum, sequentialWeight]
    · rw [sequentialSum, if_neg hm, ih, Finset.sum_range_succ]
      have hw : ∀ i < m, sequentialWeight δ (m+1) i =
          sequentialWeight δ m i * (1 + δ m) := by
        intro i hi
        unfold sequentialWeight
        rw [Finset.prod_Ico_succ_top (by omega)]
      have hl : sequentialWeight δ (m+1) m = 1 + δ m := by
        have : max 1 m = m := max_eq_right (by omega)
        simp [sequentialWeight, this]
      rw [hl, add_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hw i (Finset.mem_range.mp hi)]
      ring

lemma gamma_mono {a b : ℕ} {u : ℝ} (hu : 0 ≤ u) (hab : a ≤ b)
    (hb : (b : ℝ) * u < 1) : gamma a u ≤ gamma b u := by
  have hab' : (a : ℝ) * u ≤ (b : ℝ) * u :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hu
  unfold gamma
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

lemma gamma_step {m : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (h : ((m+1 : ℕ) : ℝ) * u < 1) :
    gamma m u * (1+u) + u ≤ gamma (m+1) u := by
  have hm : (m : ℝ) * u < 1 := by
    push_cast at h
    nlinarith
  have hp : 0 < 1 - (m : ℝ) * u := by linarith
  have hq : 0 < 1 - ((m+1 : ℕ) : ℝ) * u := by linarith
  unfold gamma
  calc
    (m : ℝ) * u / (1 - (m : ℝ) * u) * (1+u) + u =
        ((m : ℝ) * u + u) / (1 - (m : ℝ) * u) := by
      field_simp
      <;> ring
    _ ≤ ((m+1 : ℕ) : ℝ) * u / (1 - ((m+1 : ℕ) : ℝ) * u) := by
      apply (div_le_div_iff₀ hp hq).mpr
      push_cast
      nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) + 1 by positivity) (sq_nonneg u)]

lemma list_product_error (ds : List ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hd : ∀ d ∈ ds, |d| ≤ u) (hsmall : (ds.length : ℝ) * u < 1) :
    |(ds.map (fun d => 1+d)).prod - 1| ≤ gamma ds.length u := by
  induction ds with
  | nil => simp [gamma]
  | cons d ds ih =>
    have hd0 := hd d (by simp)
    have hs : (ds.length : ℝ) * u < 1 := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hsmall
      nlinarith
    have hi := ih (fun z hz => hd z (by simp [hz])) hs
    have ha : |1+d| ≤ 1+u := by
      calc
        |1+d| ≤ |(1:ℝ)| + |d| := abs_add_le _ _
        _ ≤ 1+u := by simpa using hd0
    have hg : 0 ≤ gamma ds.length u := by
      unfold gamma
      exact div_nonneg (by positivity) (by linarith)
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    calc
      |(1+d) * (ds.map (fun d => 1+d)).prod - 1| =
          |((ds.map (fun d => 1+d)).prod - 1) * (1+d) + d| := by congr 1; ring
      _ ≤ |(ds.map (fun d => 1+d)).prod - 1| * |1+d| + |d| := by
        simpa [abs_mul] using abs_add_le
          (((ds.map (fun d => 1+d)).prod - 1) * (1+d)) d
      _ ≤ gamma ds.length u * (1+u) + u := by
        exact add_le_add (mul_le_mul hi ha (abs_nonneg _) hg) hd0
      _ ≤ gamma (ds.length+1) u := gamma_step hu hsmall

lemma block_cover {n T : ℕ} (hT : 0 < T) : n ≤ blockCount n T * T := by
  have hmod := Nat.mod_lt (n+T-1) hT
  have hdiv := Nat.mod_add_div (n+T-1) T
  unfold blockCount
  nlinarith [Nat.sub_add_cancel (show 1 ≤ n+T by omega)]

lemma index_block_lt {n T : ℕ} (hT : 0 < T) (i : Fin n) :
    i.val / T < blockCount n T := by
  apply (Nat.div_lt_iff_lt_mul hT).mpr
  exact lt_of_lt_of_le i.isLt (block_cover hT)

lemma prod_map_toList (s : Finset ℕ) (f : ℕ → ℝ) :
    (s.toList.map f).prod = ∏ k ∈ s, f k := by
  exact Finset.prod_map_toList s f

lemma coefficient_bound {n T : ℕ} (hT : 0 < T) (u : ℝ) (hu : 0 ≤ u)
    (e : RoundingTrace) (hr : e.Admissible n T u)
    (hs : (errorIndex n T : ℝ) * u < 1) (i : Fin n) :
    |termCoefficient n T e i - 1| ≤ gamma (errorIndex n T) u := by
  let j := i.val / T
  let t := i.val % T
  have hj : j < blockCount n T := index_block_lt hT i
  have ht : t < T := Nat.mod_lt _ hT
  let s := Finset.Ico (max 1 t) T
  let r := Finset.Ico (max 1 j) (blockCount n T)
  let ds := e.mulError j t ::
    (s.toList.map (e.blockAddError j) ++ r.toList.map e.reductionAddError)
  have hlen : ds.length ≤ errorIndex n T := by
    simp only [ds, List.length_cons, List.length_append, List.length_map,
      Finset.length_toList, s, r, Nat.card_Ico, errorIndex]
    have : 0 < blockCount n T := lt_of_le_of_lt (Nat.zero_le j) hj
    omega
  have hds : ∀ d ∈ ds, |d| ≤ u := by
    intro d hd
    simp only [ds, List.mem_cons, List.mem_append, List.mem_map,
      Finset.mem_toList, s, r, Finset.mem_Ico] at hd
    rcases hd with h | ⟨k, ⟨hk, hk'⟩, rfl⟩ | ⟨k, ⟨hk, hk'⟩, rfl⟩
    · subst d; exact hr.1 j hj t ht
    · exact hr.2.1 j hj k (by omega) hk'
    · exact hr.2.2 k (by omega) hk'
  have hsmall : (ds.length : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hu) hs
  have hp : (ds.map (fun d => 1+d)).prod = termCoefficient n T e i := by
    simp only [ds, List.map_cons, List.map_append, List.prod_cons, List.prod_append,
      List.map_map, Function.comp_def]
    rw [prod_map_toList, prod_map_toList]
    simp only [termCoefficient, sequentialWeight, s, r, j, t]
    ring
  rw [← hp]
  exact (list_product_error ds u hu hds hsmall).trans (gamma_mono hu hlen hs)

lemma sum_rectangle (B T : ℕ) (hT : 0 < T) (f : ℕ → ℕ → ℝ) :
    (∑ j ∈ Finset.range B, ∑ t ∈ Finset.range T, f j t) =
      ∑ i ∈ Finset.range (B*T), f (i/T) (i%T) := by
  rw [← Finset.sum_product (Finset.range B) (Finset.range T)
    (fun p : ℕ × ℕ => f p.1 p.2)]
  have hdiv : ∀ j t, t < T → (j*T+t)/T = j := by
    intro j t ht
    rw [Nat.mul_comm j T, Nat.mul_add_div hT, Nat.div_eq_of_lt ht, Nat.add_zero]
  have hmod : ∀ j t, t < T → (j*T+t)%T = t := by
    intro j t ht
    rw [Nat.mul_comm j T, Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
  apply Finset.sum_bij (fun p _ => p.1*T+p.2)
  · intro p hp
    obtain ⟨hj, ht⟩ := Finset.mem_product.mp hp
    simp only [Finset.mem_range] at hj ht ⊢
    nlinarith
  · intro p hp q hq heq
    obtain ⟨hj, ht⟩ := Finset.mem_product.mp hp
    obtain ⟨hj', ht'⟩ := Finset.mem_product.mp hq
    have heq1 := congrArg (fun i => i/T) heq
    have heq2 := congrArg (fun i => i%T) heq
    dsimp only at heq1 heq2
    rw [hdiv _ _ (Finset.mem_range.mp ht), hdiv _ _ (Finset.mem_range.mp ht')] at heq1
    rw [hmod _ _ (Finset.mem_range.mp ht), hmod _ _ (Finset.mem_range.mp ht')] at heq2
    exact Prod.ext heq1 heq2
  · intro i hi
    refine ⟨(i/T, i%T), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hT).mpr (Finset.mem_range.mp hi))
      · exact Finset.mem_range.mpr (Nat.mod_lt _ hT)
    · dsimp
      nlinarith [Nat.div_add_mod i T]
  · intro p hp
    obtain ⟨hj, ht⟩ := Finset.mem_product.mp hp
    rw [hdiv _ _ (Finset.mem_range.mp ht), hmod _ _ (Finset.mem_range.mp ht)]

lemma computed_expansion {n T : ℕ} (hT : 0 < T)
    (x y : Fin n → ℝ) (e : RoundingTrace) :
    computedDot T x y e = ∑ i : Fin n, x i * y i * termCoefficient n T e i := by
  let B := blockCount n T
  let c : ℕ → ℕ → ℝ := fun j t =>
    (1 + e.mulError j t) * sequentialWeight (e.blockAddError j) T t *
      sequentialWeight e.reductionAddError B j
  have hexpand : computedDot T x y e =
      ∑ j ∈ Finset.range B, ∑ t ∈ Finset.range T,
        padded x (j*T+t) * padded y (j*T+t) * c j t := by
    unfold computedDot
    rw [sequential_expansion]
    apply Finset.sum_congr rfl
    intro j hj
    unfold blockPartial
    rw [sequential_expansion, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp [roundedProduct, c]
    ring
  rw [hexpand]
  have hflatten :
      (∑ j ∈ Finset.range B, ∑ t ∈ Finset.range T,
        padded x (j*T+t) * padded y (j*T+t) * c j t) =
      ∑ i ∈ Finset.range (B*T), padded x i * padded y i * c (i/T) (i%T) := by
    rw [sum_rectangle B T hT]
    apply Finset.sum_congr rfl
    intro i hi
    have heq : i/T*T+i%T = i := by nlinarith [Nat.div_add_mod i T]
    rw [heq]
  rw [hflatten]
  have htrunc :
      (∑ i ∈ Finset.range n, padded x i * padded y i * c (i/T) (i%T)) =
      ∑ i ∈ Finset.range (B*T), padded x i * padded y i * c (i/T) (i%T) := by
    apply Finset.sum_subset
    · exact Finset.range_mono (block_cover hT)
    · intro i hi hn
      have hn' : ¬ i < n := by simpa using hn
      simp [padded, hn']
  rw [← htrunc, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  simp [padded, hi', c, B, termCoefficient]

/-- Constructive form of the selected corollary. Both perturbations are
explicitly defined from the operations actually executed. The two identities
are alternative backward representations of the same computed result. -/
theorem constructed_backward_errors
    {n T : ℕ} (hT : 0 < T) (u : ℝ) (hu : 0 ≤ u)
    (x y : Fin n → ℝ) (e : RoundingTrace)
    (hround : e.Admissible n T u)
    (htree : ((T + treeDepth n T : ℕ) : ℝ) * u < 1)
    (hsequential : (errorIndex n T : ℝ) * u < 1) :
    (computedDot T x y e =
      ∑ i : Fin n, (x i + backwardPerturbation T e x i) * y i) ∧
    (∀ i : Fin n, |backwardPerturbation T e x i| ≤
      gamma (errorIndex n T) u * |x i|) ∧
    (computedDot T x y e =
      ∑ i : Fin n, x i * (y i + backwardPerturbation T e y i)) ∧
    (∀ i : Fin n, |backwardPerturbation T e y i| ≤
      gamma (errorIndex n T) u * |y i|) := by
  have hexpand := computed_expansion hT x y e
  have hb : ∀ i : Fin n, |termCoefficient n T e i - 1| ≤
      gamma (errorIndex n T) u := coefficient_bound hT u hu e hround hsequential
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hexpand]
    apply Finset.sum_congr rfl
    intro i hi
    unfold backwardPerturbation
    ring
  · intro i
    change |(termCoefficient n T e i - 1) * x i| ≤ _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hb i) (abs_nonneg _)
  · rw [hexpand]
    apply Finset.sum_congr rfl
    intro i hi
    unfold backwardPerturbation
    ring
  · intro i
    change |(termCoefficient n T e i - 1) * y i| ≤ _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hb i) (abs_nonneg _)

/-- `corollary:block_dot_product_sequential` (main.tex/paper.tex lines 312–343).
The dot product can be represented by perturbing either original vector,
with the exact constant `γ_(T+⌈n/T⌉-1)` and componentwise bounds. -/
theorem block_dot_product_sequential
    {n T : ℕ} (hT : 0 < T) (u : ℝ) (hu : 0 ≤ u)
    (x y : Fin n → ℝ) (e : RoundingTrace)
    (hround : e.Admissible n T u)
    (htree : ((T + treeDepth n T : ℕ) : ℝ) * u < 1)
    (hsequential : (errorIndex n T : ℝ) * u < 1) :
    ∃ Δx Δy : Fin n → ℝ,
      (computedDot T x y e = ∑ i : Fin n, (x i + Δx i) * y i) ∧
      (∀ i : Fin n, |Δx i| ≤ gamma (errorIndex n T) u * |x i|) ∧
      (computedDot T x y e = ∑ i : Fin n, x i * (y i + Δy i)) ∧
      (∀ i : Fin n, |Δy i| ≤ gamma (errorIndex n T) u * |y i|) := by
  exact ⟨backwardPerturbation T e x, backwardPerturbation T e y,
    constructed_backward_errors hT u hu x y e hround htree hsequential⟩

end

end Research.BlockDotProduct
