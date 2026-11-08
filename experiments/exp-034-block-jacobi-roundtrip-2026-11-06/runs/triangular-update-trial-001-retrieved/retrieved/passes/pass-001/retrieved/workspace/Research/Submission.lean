import Mathlib

/-!
Formalization of `lemma:traingular_update` in the supplied paper.
All vectors use zero-based indexing. The standard relative-error model applies
to every operation below; its bounded-error hypotheses express the source's
no-overflow/no-underflow assumption. The first product initializes the sum,
so there is no spurious rounding of an addition to zero.
-/

namespace TriangularUpdate

noncomputable section

open scoped BigOperators

/-- The deterministic rounding-error constant from the source. -/
def gamma (k : ℕ) (u : ℝ) : ℝ := (k : ℝ) * u / (1 - (k : ℝ) * u)

/-- Extend a finite vector by zero, only to give the recurrence a total body.
The computation and the weight products access only coordinates below `k`. -/
def entry {k : ℕ} (v : Fin k → ℝ) (i : ℕ) : ℝ :=
  if h : i < k then v ⟨i, h⟩ else 0

/-- The source's coordinate `k`, in zero-based indexing. -/
def lastIndex (k : ℕ) (hk : 0 < k) : Fin k :=
  ⟨k - 1, by omega⟩

/-- Rounded individual product at zero-based coordinate `i`. -/
def roundedProduct {k : ℕ} (a b ξ : Fin k → ℝ) (i : ℕ) : ℝ :=
  entry a i * entry b i * (1 + entry ξ i)

/-- Sequential inner product of the first `m` coordinates. Only `m ≤ k - 1`
is used by the triangular kernel. `δ 0` is unused because initialization is
the first rounded product itself. -/
def sequentialDot {k : ℕ} (a b ξ δ : Fin k → ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 =>
    if m = 0 then roundedProduct a b ξ m
    else (sequentialDot a b ξ δ m + roundedProduct a b ξ m) * (1 + entry δ m)

/-- Actual computed result: sequential dot product, rounded subtraction,
then rounded division, in precisely that order. -/
def computedValue {k : ℕ} (hk : 0 < k) (a b ξ δ : Fin k → ℝ)
    (c η ζ : ℝ) : ℝ :=
  (((c - sequentialDot a b ξ δ (k - 1)) * (1 + η)) / b (lastIndex k hk)) *
    (1 + ζ)

/-- Local errors for every active multiplication and addition, and for the
final subtraction and division. Unused coordinates have no constraints. -/
def LocalErrors {k : ℕ} (u : ℝ) (ξ δ : Fin k → ℝ) (η ζ : ℝ) : Prop :=
  (∀ i : Fin k, i.val < k - 1 → |ξ i| ≤ u) ∧
  (∀ i : Fin k, 1 ≤ i.val → i.val < k - 1 → |δ i| ≤ u) ∧
  |η| ≤ u ∧ |ζ| ≤ u

/-- A possible floating-point evaluation under the standard relative-error
model. No backward-error conclusion is assumed in this relation. -/
def IsEvaluation {k : ℕ} (hk : 0 < k) (u : ℝ) (a b : Fin k → ℝ)
    (c yhat : ℝ) : Prop :=
  ∃ (ξ δ : Fin k → ℝ) (η ζ : ℝ),
    LocalErrors u ξ δ η ζ ∧ yhat = computedValue hk a b ξ δ c η ζ

/-- Rounding factors multiplying an original inner-product term. The range
is zero-based: additions run from `max 1 i.val` through `k - 2`. -/
def dotWeight {k : ℕ} (ξ δ : Fin k → ℝ) (i : Fin k) : ℝ :=
  (1 + ξ i) *
    ∏ j ∈ (Finset.range (k - 1)).filter (fun j => 1 ≤ j ∧ i.val ≤ j),
      (1 + entry δ j)

/-- The last coordinate absorbs the inverses of the final two factors. -/
def finalWeight (η ζ : ℝ) : ℝ := ((1 + η) * (1 + ζ))⁻¹

/-- Explicit perturbation of the original vector `b`, using realized local
errors. This has a concrete body, including when a coordinate of `b` is zero. -/
def perturbation {k : ℕ} (b ξ δ : Fin k → ℝ) (η ζ : ℝ) : Fin k → ℝ :=
  fun i => b i *
    ((if i.val < k - 1 then dotWeight ξ δ i else finalWeight η ζ) - 1)

/-- The exact equation requested in the source, with no `a` term at the final
coordinate. -/
def BackwardEquation {k : ℕ} (hk : 0 < k) (a b Δb : Fin k → ℝ)
    (c yhat : ℝ) : Prop :=
  (∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < k - 1),
      a i * (b i + Δb i)) +
    yhat * (b (lastIndex k hk) + Δb (lastIndex k hk)) = c

lemma product_interval {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hs : (s.card : ℝ) * u < 1)
    (hf : ∀ i ∈ s, 1 - u ≤ f i ∧ f i ≤ 1 / (1 - u)) :
    1 - (s.card : ℝ) * u ≤ ∏ i ∈ s, f i ∧
      (∏ i ∈ s, f i) ≤ 1 / (1 - (s.card : ℝ) * u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hc : ((insert a s).card : ℝ) = (s.card : ℝ) + 1 := by
      simp [Finset.card_insert_of_notMem ha]
    rw [hc] at hs ⊢
    have hs' : (s.card : ℝ) * u < 1 := by nlinarith
    have hu1 : u < 1 := by
      have : 0 ≤ (s.card : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
      nlinarith
    have hd : 0 < 1 - (s.card : ℝ) * u := by linarith
    have he : 0 < 1 - u := by linarith
    have ht : 0 < 1 - ((s.card : ℝ) + 1) * u := by linarith
    obtain ⟨hl, hr⟩ := ih hs' (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    obtain ⟨hal, har⟩ := hf a (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert ha]
    constructor
    · have h := mul_le_mul hal hl (le_of_lt hd) (le_trans (le_of_lt he) hal)
      have hn : 0 ≤ (s.card : ℝ) * u * u := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) hu
      nlinarith
    · calc
        f a * ∏ i ∈ s, f i ≤ (1 / (1-u)) * (1 / (1-(s.card : ℝ)*u)) :=
          mul_le_mul har hr (le_trans (le_of_lt hd) hl) (le_of_lt (one_div_pos.mpr he))
        _ = 1 / ((1-u)*(1-(s.card : ℝ)*u))  := by rw [one_div, one_div, one_div, mul_inv]
        _ ≤ 1 / (1-((s.card : ℝ)+1)*u) := by
          apply one_div_le_one_div_of_le ht
          have hn : 0 ≤ (s.card : ℝ) * u * u := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) hu
          nlinarith

lemma product_gamma {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (k : ℕ) (u : ℝ) (hu : 0 ≤ u) (hk : (k : ℝ)*u < 1)
    (hc : s.card ≤ k)
    (hf : ∀ i ∈ s, 1-u ≤ f i ∧ f i ≤ 1/(1-u)) :
    |(∏ i ∈ s, f i) - 1| ≤ gamma k u := by
  have hck : (s.card : ℝ)*u ≤ (k : ℝ)*u := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hu
  have hd : 0 < 1 - (k : ℝ)*u := by linarith
  obtain ⟨hl, hr⟩ := product_interval s f u hu (lt_of_le_of_lt hck hk) hf
  have hn : 0 ≤ (k : ℝ)*u := mul_nonneg (Nat.cast_nonneg _) hu
  have hg : (k : ℝ)*u ≤ gamma k u := by
    unfold gamma
    apply (le_div_iff₀ hd).2
    nlinarith
  apply abs_le.mpr
  constructor
  · linarith
  · have hr' : (∏ i ∈ s, f i) ≤ 1/(1-(k : ℝ)*u) := hr.trans
        (one_div_le_one_div_of_le hd (by linarith))
    have heq : 1/(1-(k : ℝ)*u) - 1 = gamma k u := by
      unfold gamma
      field_simp
      ring
    linarith

lemma factor_interval (u e : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) (he : |e| ≤ u) :
    1-u ≤ 1+e ∧ 1+e ≤ 1/(1-u) := by
  obtain ⟨hel, her⟩ := abs_le.mp he
  constructor
  · linarith
  · apply (le_div_iff₀ (by linarith : 0 < 1-u)).2
    nlinarith [sq_nonneg u]

lemma inverse_factor_interval (u e : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) (he : |e| ≤ u) :
    1-u ≤ (1+e)⁻¹ ∧ (1+e)⁻¹ ≤ 1/(1-u) := by
  obtain ⟨hl, hr⟩ := factor_interval u e hu hu1 he
  have hp : 0 < 1+e := by linarith
  constructor
  · rw [← one_div]
    apply (le_div_iff₀ hp).2
    simpa only [mul_comm] using (le_div_iff₀ (by linarith : 0 < 1-u)).1 hr
  · simpa only [one_div] using one_div_le_one_div_of_le (by linarith : 0 < 1-u) hl

lemma sequential_expansion {k : ℕ} (a b ξ δ : Fin k → ℝ) (m : ℕ) :
    sequentialDot a b ξ δ m =
      ∑ i ∈ Finset.range m, roundedProduct a b ξ i *
        ∏ j ∈ (Finset.range m).filter (fun j => 1 ≤ j ∧ i ≤ j), (1 + entry δ j) := by
  classical
  induction m with
  | zero => simp [sequentialDot]
  | succ m ih =>
    by_cases hm : m = 0
    · subst m; norm_num [sequentialDot, Finset.prod_filter]
    · have hm1 : 1 ≤ m := by omega
      rw [sequentialDot, if_neg hm, ih, Finset.sum_range_succ, add_mul, Finset.sum_mul]
      have hold : ∀ i ∈ Finset.range m,
          (∏ j ∈ (Finset.range (m+1)).filter (fun j => 1 ≤ j ∧ i ≤ j), (1+entry δ j)) =
          (1+entry δ m) * ∏ j ∈ (Finset.range m).filter (fun j => 1 ≤ j ∧ i ≤ j), (1+entry δ j) := by
        intro i hi
        have him : i ≤ m := by have := Finset.mem_range.mp hi; omega
        simp [Finset.range_add_one, Finset.filter_insert, hm1, him]
      have hnew : (Finset.range (m+1)).filter (fun j => 1 ≤ j ∧ m ≤ j) = {m} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        omega
      rw [hnew]
      simp only [Finset.prod_singleton]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hold i hi]
      ring

lemma dotWeight_gamma {k : ℕ} (hk : 2 ≤ k) (u : ℝ) (hu : 0 ≤ u)
    (hku : (k : ℝ)*u < 1) (ξ δ : Fin k → ℝ) (η ζ : ℝ)
    (herr : LocalErrors u ξ δ η ζ) (i : Fin k) (hi : i.val < k-1) :
    |dotWeight ξ δ i - 1| ≤ gamma k u := by
  classical
  let s := (Finset.range (k-1)).filter (fun j => 1 ≤ j ∧ i.val ≤ j)
  let f : ℕ → ℝ := fun j => if j = 0 then 1 + ξ i else 1 + entry δ j
  have h0 : 0 ∉ s := by simp [s]
  have heq : dotWeight ξ δ i = ∏ j ∈ insert 0 s, f j := by
    rw [Finset.prod_insert h0]
    simp only [f, if_pos rfl]
    unfold dotWeight
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_filter.mp hj).2.1
    simp only [if_neg (by omega : j ≠ 0)]
  rw [heq]
  apply product_gamma _ _ k u hu hku
  · have hsub : insert 0 s ⊆ Finset.range (k-1) := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simp; omega
      · exact (Finset.mem_filter.mp hj).1
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_range] at hc
    omega
  · intro j hj
    have hu1 : u < 1 := by
      have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      nlinarith
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simpa only [f, if_pos rfl] using factor_interval u (ξ i) hu hu1 (herr.1 i hi)
    · have hj' := Finset.mem_filter.mp hj
      have hjk : j < k := by have := Finset.mem_range.mp hj'.1; omega
      have he : |entry δ j| ≤ u := by
        simpa [entry, hjk] using herr.2.1 ⟨j, hjk⟩ hj'.2.1 (Finset.mem_range.mp hj'.1)
      simpa only [f, if_neg (by have := hj'.2.1; omega : j ≠ 0)] using
        factor_interval u (entry δ j) hu hu1 he

lemma finalWeight_gamma (k : ℕ) (hk : 2 ≤ k) (u : ℝ) (hu : 0 ≤ u)
    (hku : (k : ℝ)*u < 1) (η ζ : ℝ) (hη : |η| ≤ u) (hζ : |ζ| ≤ u) :
    |finalWeight η ζ - 1| ≤ gamma k u := by
  have hu1 : u < 1 := by
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    nlinarith
  have hh := product_gamma (Finset.univ : Finset (Fin 2))
    (fun i => if i = 0 then (1+η)⁻¹ else (1+ζ)⁻¹) k u hu hku
    (by simpa using hk)
    (by
      intro i hi
      dsimp only
      split_ifs
      · exact inverse_factor_interval u η hu hu1 hη
      · exact inverse_factor_interval u ζ hu hu1 hζ)
  simpa [finalWeight, Fin.prod_univ_two, mul_inv, mul_comm] using hh

lemma dot_expansion {k : ℕ} (a b ξ δ : Fin k → ℝ) :
    sequentialDot a b ξ δ (k-1) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < k-1),
        a i * (b i * dotWeight ξ δ i) := by
  classical
  rw [sequential_expansion]
  apply Finset.sum_bij (fun i hi => (⟨i, by have := Finset.mem_range.mp hi; omega⟩ : Fin k))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_range.mp hi
  · intro i hi j hj hij
    exact congrArg Fin.val hij
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    exact ⟨i.val, Finset.mem_range.mpr hi', by simp⟩
  · intro i hi
    have hik : i < k := by have := Finset.mem_range.mp hi; omega
    simp only [roundedProduct, entry, dif_pos hik, dotWeight]
    ring

/-- Constructive form of the full triangular-update bound. Proof scaffolding
is intentionally left for the next role; none of the definitions is a hole. -/
theorem triangular_update_constructed
    (k : ℕ) (hk : 2 ≤ k) (u : ℝ) (hu : 0 ≤ u) (hku : (k : ℝ) * u < 1)
    (a b : Fin k → ℝ) (c : ℝ)
    (hb : b (lastIndex k (by omega)) ≠ 0)
    (ξ δ : Fin k → ℝ) (η ζ : ℝ) (herr : LocalErrors u ξ δ η ζ) :
    BackwardEquation (by omega) a b (perturbation b ξ δ η ζ) c
      (computedValue (by omega) a b ξ δ c η ζ) ∧
    ∀ i : Fin k, |perturbation b ξ δ η ζ i| ≤ gamma k u * |b i| := by
  classical
  have hu1 : u < 1 := by
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    nlinarith
  have hη : 1 + η ≠ 0 := ne_of_gt (by
    have := (abs_le.mp herr.2.2.1).1
    linarith)
  have hζ : 1 + ζ ≠ 0 := ne_of_gt (by
    have := (abs_le.mp herr.2.2.2).1
    linarith)
  have hpert (i : Fin k) : b i + perturbation b ξ δ η ζ i =
      b i * (if i.val < k-1 then dotWeight ξ δ i else finalWeight η ζ) := by
    unfold perturbation
    ring
  constructor
  · unfold BackwardEquation
    have hsum : (∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < k-1),
        a i * (b i + perturbation b ξ δ η ζ i)) = sequentialDot a b ξ δ (k-1) := by
      rw [dot_expansion]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hpert, if_pos (Finset.mem_filter.mp hi).2]
    rw [hsum, hpert]
    have hlast : ¬ (lastIndex k (by omega)).val < k-1 := by
      simp [lastIndex]
    rw [if_neg hlast]
    unfold computedValue finalWeight
    field_simp
    ring
  · intro i
    rw [perturbation, abs_mul]
    have hw : |(if i.val < k-1 then dotWeight ξ δ i else finalWeight η ζ) - 1| ≤
        gamma k u := by
      split_ifs with hi
      · exact dotWeight_gamma hk u hu hku ξ δ η ζ herr i hi
      · exact finalWeight_gamma k hk u hu hku η ζ herr.2.2.1 herr.2.2.2
    calc
      |b i| * |(if i.val < k-1 then dotWeight ξ δ i else finalWeight η ζ) - 1| ≤
          |b i| * gamma k u := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
      _ = gamma k u * |b i| := mul_comm _ _

/-- The complete selected lemma: every sequential floating-point evaluation
admits one perturbation vector satisfying both the exact equation and every
componentwise `gamma k u` bound simultaneously. -/
theorem triangular_update
    (k : ℕ) (hk : 2 ≤ k) (u : ℝ) (hu : 0 ≤ u) (hku : (k : ℝ) * u < 1)
    (a b : Fin k → ℝ) (c yhat : ℝ)
    (hb : b (lastIndex k (by omega)) ≠ 0)
    (heval : IsEvaluation (by omega) u a b c yhat) :
    ∃ Δb : Fin k → ℝ,
      BackwardEquation (by omega) a b Δb c yhat ∧
      ∀ i : Fin k, |Δb i| ≤ gamma k u * |b i| := by
  obtain ⟨ξ, δ, η, ζ, herr, rfl⟩ := heval
  exact ⟨perturbation b ξ δ η ζ,
    triangular_update_constructed k hk u hu hku a b c hb ξ δ η ζ herr⟩

end

end TriangularUpdate
