import Mathlib

/-!
# Triangular update: statement and explicit constructions

Source: `Sources/source.txt`, selected lemma `lemma:traingular_update`;
original proof: `Sources/paper.tex`, lines 403–452.

All vectors use zero-based `Fin k` indices. Thus the paper's coordinate i
corresponds to Lean coordinate i-1. A trace contains the elementary relative
errors of the specified sequential evaluation. `ErrorTrace.Valid` represents
the standard rounding model when no overflow or underflow occurs; it does
not postulate any bound on the accumulated error. Nonnegative unit roundoff
is the contextual convention inherent in that model.

Only the final theorem proof is left as scaffolding for the proving role.
-/

namespace Research.TriangularUpdate

/-- The deterministic error constant from the source. -/
noncomputable def gamma (k : ℕ) (u : ℝ) : ℝ :=
  (k : ℝ) * u / (1 - (k : ℝ) * u)

/-- Relative errors of each multiplication, each possible accumulator addition,
then the final subtraction and division. Addition at index zero is unused. -/
structure ErrorTrace (k : ℕ) where
  mulError : Fin (k - 1) → ℝ
  addError : Fin (k - 1) → ℝ
  subError : ℝ
  divError : ℝ

/-- Bounds only on errors of executed elementary operations. In particular,
there is no rounded addition before the first product. -/
def ErrorTrace.Valid {k : ℕ} (e : ErrorTrace k) (u : ℝ) : Prop :=
  (∀ i, |e.mulError i| ≤ u) ∧
  (∀ j, 0 < j.val → |e.addError j| ≤ u) ∧
  |e.subError| ≤ u ∧ |e.divError| ≤ u

/-- Embed one of the first k-1 coordinates into the full input vector. -/
def prefixIndex {k : ℕ} (i : Fin (k - 1)) : Fin k :=
  ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le k 1)⟩

/-- The paper's last coordinate k, using zero-based indexing. -/
def lastIndex (k : ℕ) (hk : 2 ≤ k) : Fin k :=
  ⟨k - 1, by omega⟩

/-- Rounded individual product, tied to the original inputs. -/
noncomputable def roundedProduct {k : ℕ} (a b : Fin k → ℝ)
    (e : ErrorTrace k) (i : Fin (k - 1)) : ℝ :=
  (a (prefixIndex i) * b (prefixIndex i)) * (1 + e.mulError i)

/-- Sequential accumulator after n terms. The first term is its rounded
product alone; each subsequent term incurs one addition error. Values beyond
the input length are defined by keeping the completed accumulator. -/
noncomputable def sequentialAccumulator {k : ℕ} (a b : Fin k → ℝ)
    (e : ErrorTrace k) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      if h : n < k - 1 then
        if n = 0 then roundedProduct a b e ⟨n, h⟩
        else (sequentialAccumulator a b e n + roundedProduct a b e ⟨n, h⟩) *
          (1 + e.addError ⟨n, h⟩)
      else sequentialAccumulator a b e n

/-- The computed inner product of the first k-1 entries. -/
noncomputable def sequentialInnerProduct {k : ℕ} (a b : Fin k → ℝ)
    (e : ErrorTrace k) : ℝ :=
  sequentialAccumulator a b e (k - 1)

/-- Rounded subtraction following the inner product. -/
noncomputable def roundedNumerator {k : ℕ} (a b : Fin k → ℝ)
    (c : ℝ) (e : ErrorTrace k) : ℝ :=
  (c - sequentialInnerProduct a b e) * (1 + e.subError)

/-- Actual result of the sequential inner product, subtraction, and division. -/
noncomputable def computedUpdate {k : ℕ} (hk : 2 ≤ k) (a b : Fin k → ℝ)
    (c : ℝ) (e : ErrorTrace k) : ℝ :=
  (roundedNumerator a b c e / b (lastIndex k hk)) * (1 + e.divError)

/-- Coefficient of an inner-product term after all subsequent additions.
The filter is the zero-based form of j = max(2,i),...,k-1 in the paper. -/
noncomputable def innerCoefficient {k : ℕ} (e : ErrorTrace k)
    (i : Fin (k - 1)) : ℝ :=
  (1 + e.mulError i) *
    ∏ j ∈ (Finset.univ.filter (fun j : Fin (k - 1) => 0 < j.val ∧ i.val ≤ j.val)),
      (1 + e.addError j)

/-- The coefficient on the last input is the reciprocal of the two final
rounding factors, as required by the backward equation. -/
noncomputable def lastCoefficient {k : ℕ} (e : ErrorTrace k) : ℝ :=
  ((1 + e.subError) * (1 + e.divError))⁻¹

/-- One explicit perturbation vector on the original b. Zero input components
receive zero perturbation; no division by an inner-product component occurs. -/
noncomputable def perturbation {k : ℕ} (b : Fin k → ℝ)
    (e : ErrorTrace k) (i : Fin k) : ℝ :=
  if h : i.val < k - 1 then
    b i * (innerCoefficient e ⟨i.val, h⟩ - 1)
  else
    b i * (lastCoefficient e - 1)

/-- Elementary product bounds, proved from the individual rounding errors. -/
lemma product_bounds {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ) (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1)
    (hf : ∀ i ∈ s, |f i - 1| ≤ u) (hn : (s.card : ℝ) * u < 1) :
    1 - (s.card : ℝ) * u ≤ ∏ i ∈ s, f i ∧
    (∏ i ∈ s, f i) ≤ (1 - (s.card : ℝ) * u)⁻¹ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    have hc : ((insert x s).card : ℝ) = (s.card : ℝ) + 1 := by
      simp [Finset.card_insert_of_notMem hx]
    have hs : (s.card : ℝ) * u < 1 := by rw [hc] at hn; nlinarith
    have hfs : ∀ i ∈ s, |f i - 1| ≤ u := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    obtain ⟨hl, hr⟩ := ih hfs hs
    have hfx0 := abs_le.mp (hf x (Finset.mem_insert_self x s))
    have hfx : 1 - u ≤ f x ∧ f x ≤ 1 + u := by constructor <;> linarith
    have hp : 0 < 1 - (s.card : ℝ) * u := by linarith
    have hq : 0 < 1 - ((s.card : ℝ) + 1) * u := by rw [hc] at hn; linarith
    have hsp : 0 ≤ (s.card : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
    rw [Finset.prod_insert hx, hc]
    constructor
    · have hm := mul_le_mul hl hfx.1 (by linarith : 0 ≤ 1 - u) (by linarith : 0 ≤ ∏ i ∈ s, f i)
      nlinarith
    · have hm : f x * (∏ i ∈ s, f i) ≤ (1 + u) * (1 - (s.card : ℝ) * u)⁻¹ :=
        mul_le_mul hfx.2 hr (by linarith) (by positivity)
      apply hm.trans
      rw [inv_eq_one_div, inv_eq_one_div, mul_one_div]
      apply (div_le_div_iff₀ hp hq).2
      nlinarith [mul_nonneg hsp hu]

lemma coefficient_bound {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ) (k : ℕ) (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1)
    (hf : ∀ i ∈ s, |f i - 1| ≤ u) (hcard : s.card ≤ k)
    (hk : (k : ℝ) * u < 1) :
    |(∏ i ∈ s, f i) - 1| ≤ gamma k u := by
  have hcount : (s.card : ℝ) * u ≤ (k : ℝ) * u :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hu
  obtain ⟨hl, hr⟩ := product_bounds s f u hu hu1 hf (lt_of_le_of_lt hcount hk)
  have hp : 0 < 1 - (k : ℝ) * u := by linarith
  have hsp : 0 < 1 - (s.card : ℝ) * u := by linarith
  have hnon : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hg : (k : ℝ) * u ≤ gamma k u := by
    unfold gamma
    apply (le_div_iff₀ hp).2
    nlinarith [sq_nonneg ((k : ℝ) * u)]
  have hr' : (∏ i ∈ s, f i) ≤ (1 - (k : ℝ) * u)⁻¹ :=
    hr.trans (inv_anti₀ hp (by linarith))
  apply abs_le.mpr
  constructor
  · linarith
  · have hid : (1 - (k : ℝ) * u)⁻¹ - 1 = gamma k u := by
      unfold gamma
      field_simp
      ring
    linarith

lemma innerCoefficient_bound {k : ℕ} (hk : 2 ≤ k) (e : ErrorTrace k)
    (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) (hku : (k : ℝ) * u < 1)
    (he : e.Valid u) (i : Fin (k - 1)) :
    |innerCoefficient e i - 1| ≤ gamma k u := by
  classical
  let f : Option (Fin (k - 1)) → ℝ := fun x => match x with
    | none => 1 + e.mulError i
    | some j => if 0 < j.val ∧ i.val ≤ j.val then 1 + e.addError j else 1
  have hf : ∀ x ∈ Finset.univ, |f x - 1| ≤ u := by
    intro x hx
    cases x with
    | none => simpa [f] using he.1 i
    | some j =>
      dsimp [f]
      split_ifs with h
      · simpa using he.2.1 j h.1
      · simpa using hu
  have hc : (Finset.univ : Finset (Option (Fin (k - 1)))).card ≤ k := by
    simp only [Finset.card_univ, Fintype.card_option, Fintype.card_fin]
    omega
  have hb := coefficient_bound Finset.univ f k u hu hu1 hf hc hku
  simpa [f, Fintype.prod_option, innerCoefficient, Finset.prod_filter] using hb

lemma inverse_product_bound {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ) (k : ℕ) (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1)
    (hf : ∀ i ∈ s, |f i - 1| ≤ u) (hcard : s.card ≤ k)
    (hk : (k : ℝ) * u < 1) :
    |(∏ i ∈ s, f i)⁻¹ - 1| ≤ gamma k u := by
  have hcount : (s.card : ℝ) * u ≤ (k : ℝ) * u :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hu
  obtain ⟨hl, hr⟩ := product_bounds s f u hu hu1 hf (lt_of_le_of_lt hcount hk)
  have hp : 0 < 1 - (k : ℝ) * u := by linarith
  have hl' : 1 - (k : ℝ) * u ≤ ∏ i ∈ s, f i := by linarith
  have hprod : 0 < ∏ i ∈ s, f i := lt_of_lt_of_le hp hl'
  have hr' : (∏ i ∈ s, f i) ≤ (1 - (k : ℝ) * u)⁻¹ :=
    hr.trans (inv_anti₀ hp (by linarith))
  have hil : 1 - (k : ℝ) * u ≤ (∏ i ∈ s, f i)⁻¹ := by
    simpa using inv_anti₀ hprod hr'
  have hir : (∏ i ∈ s, f i)⁻¹ ≤ (1 - (k : ℝ) * u)⁻¹ := inv_anti₀ hp hl'
  have hg : (k : ℝ) * u ≤ gamma k u := by
    unfold gamma
    apply (le_div_iff₀ hp).2
    nlinarith [sq_nonneg ((k : ℝ) * u)]
  have hid : (1 - (k : ℝ) * u)⁻¹ - 1 = gamma k u := by
    unfold gamma
    field_simp
    ring
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma lastCoefficient_bound {k : ℕ} (hk : 2 ≤ k) (e : ErrorTrace k)
    (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) (hku : (k : ℝ) * u < 1)
    (he : e.Valid u) : |lastCoefficient e - 1| ≤ gamma k u := by
  let f : Bool → ℝ := fun x => if x then 1 + e.subError else 1 + e.divError
  have hf : ∀ x ∈ Finset.univ, |f x - 1| ≤ u := by
    intro x hx
    cases x <;> simp [f, he.2.2.1, he.2.2.2]
  have h := inverse_product_bound Finset.univ f k u hu hu1 hf (by simpa) hku
  simpa [f, lastCoefficient, mul_comm] using h

noncomputable def suffixProduct {k : ℕ} (e : ErrorTrace k) (n : ℕ) : ℝ :=
  ∏ j ∈ (Finset.univ.filter (fun j : Fin (k - 1) => 0 < j.val ∧ n ≤ j.val)),
    (1 + e.addError j)

lemma accumulator_expansion {k : ℕ} (a b : Fin k → ℝ) (e : ErrorTrace k)
    (n : ℕ) (hn : n ≤ k - 1) :
    (∑ i ∈ (Finset.univ.filter (fun i : Fin (k - 1) => i.val < n)),
      a (prefixIndex i) * b (prefixIndex i) * innerCoefficient e i) =
      sequentialAccumulator a b e n * suffixProduct e n := by
  classical
  induction n with
  | zero => simp [sequentialAccumulator]
  | succ n ih =>
    have hnk : n < k - 1 := by omega
    let i : Fin (k - 1) := ⟨n, hnk⟩
    have hs : (Finset.univ.filter (fun j : Fin (k - 1) => j.val < n + 1)) =
        insert i (Finset.univ.filter (fun j : Fin (k - 1) => j.val < n)) := by
      ext j
      simp [Fin.ext_iff, i]
      omega
    have hni : i ∉ (Finset.univ.filter (fun j : Fin (k - 1) => j.val < n)) := by
      simp [i]
    have hc : a (prefixIndex i) * b (prefixIndex i) * innerCoefficient e i =
        roundedProduct a b e i * suffixProduct e n := by
      simp only [innerCoefficient, roundedProduct, suffixProduct]
      dsimp [i]
      ring
    rw [hs, Finset.sum_insert hni, ih (by omega), hc]
    by_cases hz : n = 0
    · subst n
      have heq : suffixProduct e 0 = suffixProduct e 1 := by
        unfold suffixProduct
        congr 1
        ext j
        simp
        omega
      simp only [sequentialAccumulator, dif_pos hnk, ↓reduceIte, zero_add, zero_mul,
        add_zero]
      simp [i, heq]
    · have hsf : (Finset.univ.filter (fun j : Fin (k - 1) => 0 < j.val ∧ n ≤ j.val)) =
          insert i (Finset.univ.filter (fun j : Fin (k - 1) => 0 < j.val ∧ n + 1 ≤ j.val)) := by
        ext j
        simp [Fin.ext_iff, i]
        omega
      have hnot : i ∉ (Finset.univ.filter (fun j : Fin (k - 1) =>
          0 < j.val ∧ n + 1 ≤ j.val)) := by simp [i]
      have hsf' : suffixProduct e n = (1 + e.addError i) * suffixProduct e (n + 1) := by
        unfold suffixProduct
        rw [hsf, Finset.prod_insert hnot]
      rw [hsf']
      simp only [sequentialAccumulator, dif_pos hnk, if_neg hz]
      change _ = ((sequentialAccumulator a b e n + roundedProduct a b e i) *
        (1 + e.addError i)) * suffixProduct e (n + 1)
      ring

lemma innerProduct_expansion {k : ℕ} (a b : Fin k → ℝ) (e : ErrorTrace k) :
    sequentialInnerProduct a b e =
      ∑ i : Fin (k - 1), a (prefixIndex i) * b (prefixIndex i) * innerCoefficient e i := by
  have h := accumulator_expansion a b e (k - 1) le_rfl
  have hs : suffixProduct e (k - 1) = 1 := by
    unfold suffixProduct
    have hf : (Finset.univ.filter (fun j : Fin (k - 1) =>
        0 < j.val ∧ k - 1 ≤ j.val)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro j hj
      have := j.isLt
      omega
    rw [hf, Finset.prod_empty]
  have hf : (Finset.univ.filter (fun i : Fin (k - 1) => i.val < k - 1)) = Finset.univ := by
    ext i
    simp
  rw [hs, hf, mul_one] at h
  exact h.symm

/-- Full selected triangular-update lemma, for every legal elementary-error
trace. The explicit perturbation simultaneously satisfies the exact backward
equation and the source's componentwise gamma_k bound. -/
theorem triangular_update
    (k : ℕ) (hk : 2 ≤ k) (u : ℝ) (hu : 0 ≤ u)
    (hku : (k : ℝ) * u < 1)
    (a b : Fin k → ℝ) (c : ℝ)
    (hb : b (lastIndex k hk) ≠ 0)
    (e : ErrorTrace k) (he : e.Valid u) :
    ((∑ i : Fin (k - 1),
        a (prefixIndex i) *
          (b (prefixIndex i) + perturbation b e (prefixIndex i))) +
      computedUpdate hk a b c e *
        (b (lastIndex k hk) + perturbation b e (lastIndex k hk)) = c) ∧
    (∀ i : Fin k, |perturbation b e i| ≤ gamma k u * |b i|) := by
  classical
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hu1 : u < 1 := by nlinarith
  have hsub : 0 < 1 + e.subError := by
    have := (abs_le.mp he.2.2.1).1
    linarith
  have hdiv : 0 < 1 + e.divError := by
    have := (abs_le.mp he.2.2.2).1
    linarith
  constructor
  · have hp (i : Fin (k - 1)) :
        b (prefixIndex i) + perturbation b e (prefixIndex i) =
          b (prefixIndex i) * innerCoefficient e i := by
      simp only [perturbation, prefixIndex, dif_pos i.isLt, Fin.eta]
      ring
    have hl : b (lastIndex k hk) + perturbation b e (lastIndex k hk) =
        b (lastIndex k hk) * lastCoefficient e := by
      simp only [perturbation, lastIndex, lt_self_iff_false, ↓reduceDIte]
      ring
    have hsum : (∑ i : Fin (k - 1),
        a (prefixIndex i) * (b (prefixIndex i) + perturbation b e (prefixIndex i))) =
        sequentialInnerProduct a b e := by
      rw [innerProduct_expansion]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hp]
      ring
    rw [hsum, hl]
    have hlast : computedUpdate hk a b c e *
        (b (lastIndex k hk) * lastCoefficient e) = c - sequentialInnerProduct a b e := by
      unfold computedUpdate roundedNumerator lastCoefficient
      field_simp [hb, ne_of_gt hsub, ne_of_gt hdiv]
    rw [hlast]
    ring
  · intro i
    unfold perturbation
    split_ifs with hi
    · rw [abs_mul]
      have h := innerCoefficient_bound hk e u hu hu1 hku he ⟨i.val, hi⟩
      calc
        |b i| * |innerCoefficient e ⟨i.val, hi⟩ - 1| ≤ |b i| * gamma k u :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
        _ = gamma k u * |b i| := mul_comm _ _
    · rw [abs_mul]
      have h := lastCoefficient_bound hk e u hu hu1 hku he
      calc
        |b i| * |lastCoefficient e - 1| ≤ |b i| * gamma k u :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
        _ = gamma k u * |b i| := mul_comm _ _

end Research.TriangularUpdate
