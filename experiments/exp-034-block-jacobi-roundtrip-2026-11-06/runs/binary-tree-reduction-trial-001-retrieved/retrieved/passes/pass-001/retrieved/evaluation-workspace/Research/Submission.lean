import Mathlib

/-!
Statement skeleton for Bhola, `theorem:parallel_binary_tree_reduction`.
The supplied source files in this directory are unchanged. Indices are zero-based.
The only numerical hypothesis is the standard local addition model at operations
actually executed; this is the source's no-overflow/no-underflow model.
No feedback.json was supplied. This is the initial statement, with no revision.
-/

namespace ParallelBinaryTree

/-- Real vectors, with unrestricted finite dimension (including dimension zero). -/
abbrev Vector (d : ℕ) := Fin d → ℝ

/-- An addition implementation may depend on level, node, and component. -/
abbrev Addition (d : ℕ) := ℕ → ℕ → Fin d → ℝ → ℝ → ℝ

/-- Exactly the source depth `ceil(log₂ n)`, as a natural number for `n ≥ 1`. -/
noncomputable def depth (n : ℕ) : ℕ := ⌈Real.logb 2 (n : ℝ)⌉₊

/-- Number of active nodes at level `l`: natural ceiling division by `2^l`. -/
def width (n l : ℕ) : ℕ := (n + 2 ^ l - 1) / 2 ^ l

/-- Source deterministic roundoff constant. -/
noncomputable def gamma (l : ℕ) (u : ℝ) : ℝ := (l : ℝ) * u / (1 - (l : ℝ) * u)

/-- Actual level-by-level reduction. Unavailable entries are zero; an unpaired
active entry is copied exactly, with no floating-point addition on that branch. -/
def states {n d : ℕ} (x : Fin n → Vector d) (add : Addition d) :
    ℕ → ℕ → Vector d
  | 0, k => if h : k < n then x ⟨k, h⟩ else 0
  | l + 1, k =>
      if k < width n (l + 1) then
        if k + width n (l + 1) < width n l then
          fun c => add l k c (states x add l k c)
            (states x add l (k + width n (l + 1)) c)
        else states x add l k
      else 0

/-- Computed output is the root after precisely the prescribed number of levels. -/
noncomputable def computedResult {n d : ℕ} (x : Fin n → Vector d)
    (add : Addition d) : Vector d := states x add (depth n) 0

/-- Exact target sum of the original inputs. -/
def exactSum {n d : ℕ} (x : Fin n → Vector d) : Vector d := ∑ i, x i

/-- Standard relative-error addition model, assumed only for executed additions.
No conclusions about leaf paths, output errors, or product bounds are assumed. -/
def RoundingModel {n d : ℕ} (x : Fin n → Vector d) (add : Addition d)
    (u : ℝ) : Prop :=
  ∀ l, l < depth n → ∀ k, k < width n (l + 1) →
    k + width n (l + 1) < width n l → ∀ c : Fin d,
    ∃ δ : ℝ, |δ| ≤ u ∧
      add l k c (states x add l k c)
          (states x add l (k + width n (l + 1)) c) =
        (states x add l k c + states x add l (k + width n (l + 1)) c) * (1 + δ)

/-- Choose a relative-error witness when one exists, using zero otherwise.
This is a total definition; the model will justify the choice at actual nodes. -/
noncomputable def localError (u a b result : ℝ) : ℝ := by
  classical
  exact if h : ∃ δ : ℝ, |δ| ≤ u ∧ result = (a + b) * (1 + δ)
  then Classical.choose h else 0

/-- A carry has error zero. At an addition this selects its local model witness. -/
noncomputable def nodeError {n d : ℕ} (x : Fin n → Vector d)
    (add : Addition d) (u : ℝ) (l k : ℕ) (c : Fin d) : ℝ :=
  if k < width n (l + 1) ∧ k + width n (l + 1) < width n l then
    localError u (states x add l k c)
      (states x add l (k + width n (l + 1)) c)
      (add l k c (states x add l k c)
        (states x add l (k + width n (l + 1)) c))
  else 0

/-- Parent map for the source's split-half pairing at level `l`. -/
def parent (n l k : ℕ) : ℕ :=
  if k < width n (l + 1) then k else k - width n (l + 1)

/-- Ancestor of original input `i` after `l` levels. -/
def ancestor (n i : ℕ) : ℕ → ℕ
  | 0 => i
  | l + 1 => parent n l (ancestor n i l)

/-- Product of rounding factors along one original input's path, including
factor one on carries. Different inputs and components have different paths. -/
noncomputable def pathFactor {n d : ℕ} (x : Fin n → Vector d)
    (add : Addition d) (u : ℝ) (i : Fin n) (c : Fin d) : ℝ :=
  ∏ l ∈ Finset.range (depth n),
    (1 + nodeError x add u l (ancestor n i.val (l + 1)) c)

/-- Explicit backward perturbation of each original input component. -/
noncomputable def perturbation {n d : ℕ} (x : Fin n → Vector d)
    (add : Addition d) (u : ℝ) : Fin n → Vector d :=
  fun i c => x i c * (pathFactor x add u i c - 1)

lemma width_formula {n : ℕ} (hn : 0 < n) (l : ℕ) :
    width n l = (n - 1) / 2 ^ l + 1 := by
  have hp : 0 < 2 ^ l := pow_pos (by decide) _
  unfold width
  have he : n + 2 ^ l - 1 = (n - 1) + 2 ^ l := by omega
  rw [he, Nat.add_div_right _ hp]

lemma width_bounds {n : ℕ} (hn : 0 < n) (l : ℕ) :
    width n (l+1) ≤ width n l ∧ width n l ≤ 2 * width n (l+1) := by
  rw [width_formula hn, width_formula hn, pow_succ, ← Nat.div_div_eq_div_mul]
  have hh := Nat.mod_add_div ((n-1) / 2^l) 2
  have hr := Nat.mod_lt ((n-1) / 2^l) (by decide : 0 < 2)
  omega

lemma width_root {n : ℕ} (hn : 0 < n) : width n (depth n) = 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hnR).mp
    (Nat.le_ceil (Real.logb 2 (n : ℝ)))
  rw [Real.rpow_natCast] at h
  have hpow : n ≤ 2 ^ depth n := by
    unfold depth
    exact_mod_cast h
  rw [width_formula hn, Nat.div_eq_of_lt (by omega), zero_add]

lemma ancestor_valid {n : ℕ} (hn : 0 < n) (i : Fin n) (l : ℕ) :
    ancestor n i.val l < width n l := by
  induction l with
  | zero => simpa [ancestor, width] using i.isLt
  | succ l ih =>
    have hb := width_bounds hn l
    simp only [ancestor, parent]
    split <;> omega

lemma localError_spec (u a b r : ℝ)
    (h : ∃ δ : ℝ, |δ| ≤ u ∧ r = (a+b)*(1+δ)) :
    |localError u a b r| ≤ u ∧ r = (a+b)*(1+localError u a b r) := by
  classical
  simpa only [localError, dif_pos h] using Classical.choose_spec h

lemma nodeError_bound {n d : ℕ} (x : Fin n → Vector d) (add : Addition d)
    (u : ℝ) (hu : 0 ≤ u) (hm : RoundingModel x add u)
    (l : ℕ) (hl : l < depth n) (k : ℕ) (c : Fin d) :
    |nodeError x add u l k c| ≤ u := by
  unfold nodeError
  split
  next h => exact (localError_spec _ _ _ _ (hm l hl k h.1 h.2 c)).1
  next => simpa using hu

lemma state_step {n d : ℕ} (x : Fin n → Vector d) (add : Addition d)
    (u : ℝ) (hm : RoundingModel x add u) (l : ℕ) (hl : l < depth n)
    (k : ℕ) (hk : k < width n (l+1)) (c : Fin d) :
    states x add (l+1) k c =
      (states x add l k c +
        if k + width n (l+1) < width n l then
          states x add l (k + width n (l+1)) c else 0) *
        (1 + nodeError x add u l k c) := by
  by_cases hj : k + width n (l+1) < width n l
  · simpa [states, hk, hj, nodeError] using
      (localError_spec _ _ _ _ (hm l hl k hk hj c)).2
  · simp [states, hk, hj, nodeError]

lemma product_bound (u : ℝ) (hu : 0 ≤ u) (e : ℕ → ℝ) (m : ℕ)
    (he : ∀ j < m, |e j| ≤ u) (hs : (m : ℝ)*u < 1) :
    |(∏ j ∈ Finset.range m, (1+e j)) - 1| ≤ gamma m u := by
  induction m with
  | zero => simp [gamma]
  | succ m ih =>
    have hm : (m : ℝ)*u < 1 := by push_cast at hs; nlinarith
    have hi := ih (fun j hj => he j (by omega)) hm
    have hj := he m (by omega)
    have hd : 0 < 1 - (m : ℝ)*u := by linarith
    have hd' : 0 < 1 - ((m+1 : ℕ) : ℝ)*u := by linarith
    have hg : 0 ≤ gamma m u := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) hd.le
    have hab : |1 + e m| ≤ 1+u := by
      calc
        |1+e m| ≤ |(1 : ℝ)| + |e m| := abs_add_le _ _
        _ ≤ 1+u := by simpa using hj
    rw [Finset.prod_range_succ]
    calc
      |(∏ j ∈ Finset.range m, (1+e j)) * (1+e m) - 1| =
          |((∏ j ∈ Finset.range m, (1+e j))-1)*(1+e m)+e m| := by congr 1; ring
      _ ≤ |((∏ j ∈ Finset.range m, (1+e j))-1)*(1+e m)| + |e m| := abs_add_le _ _
      _ ≤ gamma m u * (1+u) + u := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul hi hab (abs_nonneg _) hg) hj
      _ ≤ gamma (m+1) u := by
        unfold gamma
        have hv : (↑m * u / (1 - ↑m * u) * (1 + u) + u) =
            (((m : ℝ)+1)*u) / (1-(m : ℝ)*u) := by field_simp; ring
        rw [hv]
        apply (div_le_div_iff₀ hd hd').2
        push_cast
        nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hu) hu]


noncomputable def factors {n d : ℕ} (x : Fin n → Vector d) (add : Addition d)
    (u : ℝ) (l : ℕ) (i : Fin n) (c : Fin d) : ℝ :=
  ∏ j ∈ Finset.range l, (1 + nodeError x add u j (ancestor n i.val (j+1)) c)

lemma states_zero {n d : ℕ} (x : Fin n → Vector d) (add : Addition d)
    (l k : ℕ) (hk : width n l ≤ k) : states x add l k = 0 := by
  cases l with
  | zero => simp only [width, pow_zero, Nat.add_sub_cancel, Nat.div_one] at hk
            simp [states, Nat.not_lt.mpr hk]
  | succ l => simp [states, Nat.not_lt.mpr hk]

lemma fibre (n l r k : ℕ) (hr : r < width n l)
    (hk : k < width n (l+1)) (hb : width n l ≤ 2*width n (l+1)) (v : ℝ) :
    (if parent n l r = k then v else 0) =
      (if r = k then v else 0) + (if r = k + width n (l+1) then v else 0) := by
  unfold parent
  split <;> split_ifs <;> simp_all <;> omega

lemma expansion {n d : ℕ} (hn : 0 < n) (x : Fin n → Vector d)
    (add : Addition d) (u : ℝ) (hm : RoundingModel x add u)
    (l : ℕ) (hl : l ≤ depth n) (k : ℕ) (c : Fin d) :
    states x add l k c =
      ∑ i : Fin n, if ancestor n i.val l = k then x i c * factors x add u l i c else 0 := by
  classical
  induction l generalizing k with
  | zero =>
    simp only [ancestor, factors, Finset.range_zero, Finset.prod_empty, mul_one]
    by_cases hk : k < n
    · rw [states, dif_pos hk]
      have he : ∀ i : Fin n, (i.val = k) ↔ i = ⟨k,hk⟩ := fun i => by simp [Fin.ext_iff]
      simp_rw [he]
      simp
    · rw [states, dif_neg hk]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      simp [show i.val ≠ k by have := i.isLt; omega]
  | succ l ih =>
    by_cases hk : k < width n (l+1)
    · have hstep := state_step x add u hm l (by omega) k hk c
      have hz : (if k + width n (l+1) < width n l then
          states x add l (k+width n (l+1)) c else 0) =
          states x add l (k+width n (l+1)) c := by
        split
        · rfl
        · symm; exact congrFun (states_zero x add l _ (by omega)) c
      rw [hz, ih (by omega) k, ih (by omega) (k+width n (l+1)),
        ← Finset.sum_add_distrib, Finset.sum_mul] at hstep
      rw [hstep]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← fibre n l _ k (ancestor_valid hn i l) hk (width_bounds hn l).2]
      simp only [ancestor, factors, Finset.prod_range_succ]
      by_cases ha : parent n l (ancestor n i.val l) = k
      · simp [ha]; ring
      · simp [ha]
    · rw [show states x add (l+1) k c = 0 from
        congrFun (states_zero x add (l+1) k (by omega)) c]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      have ha := ancestor_valid hn i (l+1)
      simp [show ancestor n i.val (l+1) ≠ k by omega]

/-- The stronger constructive form of the selected theorem, with the concrete
perturbations defined from the algorithm's local rounding witnesses. -/
theorem parallel_binary_tree_reduction_constructed
    {n d : ℕ} (hn : 0 < n) (x : Fin n → Vector d)
    (add : Addition d) (u : ℝ) (hu : 0 ≤ u)
    (hmodel : RoundingModel x add u) (hsmall : (depth n : ℝ) * u < 1) :
    computedResult x add = ∑ i, (x i + perturbation x add u i) ∧
      ∀ (i : Fin n) (c : Fin d),
        |perturbation x add u i c| ≤ gamma (depth n) u * |x i c| := by
  classical
  constructor
  · funext c
    have he := expansion hn x add u hmodel (depth n) le_rfl 0 c
    have ha : ∀ i : Fin n, ancestor n i.val (depth n) = 0 := by
      intro i
      have hi := ancestor_valid hn i (depth n)
      rw [width_root hn] at hi
      omega
    simp only [ha, ite_true] at he
    simp only [computedResult, Finset.sum_apply, Pi.add_apply, perturbation]
    rw [he]
    apply Finset.sum_congr rfl
    intro i hi
    change x i c * pathFactor x add u i c =
      x i c + x i c * (pathFactor x add u i c - 1)
    ring
  · intro i c
    have hp : |pathFactor x add u i c - 1| ≤ gamma (depth n) u := by
      exact product_bound u hu
        (fun l => nodeError x add u l (ancestor n i.val (l+1)) c) (depth n)
        (fun l hl => nodeError_bound x add u hu hmodel l hl _ c) hsmall
    simp only [perturbation, abs_mul]
    calc
      |x i c| * |pathFactor x add u i c - 1| ≤
          |x i c| * gamma (depth n) u := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ = gamma (depth n) u * |x i c| := mul_comm _ _

/-- Full selected theorem: componentwise backward stability of the source
binary-tree reduction, with the exact logarithmic gamma constant. -/
theorem parallel_binary_tree_reduction
    {n d : ℕ} (hn : 0 < n) (x : Fin n → Vector d)
    (add : Addition d) (u : ℝ) (hu : 0 ≤ u)
    (hmodel : RoundingModel x add u) (hsmall : (depth n : ℝ) * u < 1) :
    ∃ Δ : Fin n → Vector d,
      computedResult x add = ∑ i, (x i + Δ i) ∧
      ∀ (i : Fin n) (c : Fin d), |Δ i c| ≤ gamma (depth n) u * |x i c| := by
  exact ⟨perturbation x add u,
    parallel_binary_tree_reduction_constructed hn x add u hu hmodel hsmall⟩

end ParallelBinaryTree
