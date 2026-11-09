import Mathlib

/-!
Operation-level statement of the Cholesky backward error theorem.

`SuccessfulCholesky` is an execution relation, starting from the zero work
matrix and visiting upper-triangular entries in column order. Its witnesses
record every rounded multiplication, addition, subtraction, division, and
square root. The standard relative-error model encodes the no-overflow and
no-underflow assumption at precisely the operations performed. Square roots
explicitly obey the standard relative-error model as well.

There are no supplied supporting source files and no feedback.json. Relative
to the handoff, no mathematical conclusion has been revised. The algorithm
is specified by a complete execution relation rather than a deterministic
rounding implementation; it covers every implementation obeying the model.
-/


namespace CholeskyProof

noncomputable def g (m : ℕ) (u : ℝ) := (m : ℝ) * u / (1 - (m : ℝ) * u)

lemma g_nonneg {m : ℕ} {u : ℝ} (hu : 0 ≤ u) (h : (m : ℝ) * u < 1) :
    0 ≤ g m u := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

lemma g_mono {m n : ℕ} {u : ℝ} (hu : 0 ≤ u) (hmn : m ≤ n)
    (hn : (n : ℝ) * u < 1) : g m u ≤ g n u := by
  have hmn' : (m : ℝ) * u ≤ (n : ℝ) * u := mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hu
  unfold g
  apply (div_le_div_iff₀ (by linarith : 0 < 1 - (m : ℝ) * u) (by linarith : 0 < 1 - (n : ℝ) * u)).2
  nlinarith

lemma u_le_g {m : ℕ} {u : ℝ} (hu : 0 ≤ u) (hm : 1 ≤ m)
    (h : (m : ℝ) * u < 1) : u ≤ g m u := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold g
  apply (le_div_iff₀ (by linarith : 0 < 1 - (m : ℝ) * u)).2
  nlinarith [mul_le_mul_of_nonneg_right hm' hu, mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hu) hu]

lemma g_step {m : ℕ} {u : ℝ} (hu : 0 ≤ u) (h : ((m+1 : ℕ) : ℝ) * u < 1) :
    g m u + u + g m u * u ≤ g (m+1) u := by
  have hm : (m : ℝ) * u < 1 := by
    rw [Nat.cast_add, Nat.cast_one] at h
    nlinarith
  unfold g
  apply (le_div_iff₀ (by linarith : 0 < 1 - ((m+1 : ℕ) : ℝ) * u)).2
  have hd : 0 < 1 - (m : ℝ) * u := by linarith
  rw [Nat.cast_add, Nat.cast_one] at *
  field_simp
  -- Clearing the remaining positive denominator leaves a nonnegative multiple of u².
  nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hu) hu]

end CholeskyProof

namespace Cholesky

/-- A single rounded operation on its exact real result. -/
def Rounded (u exact computed : ℝ) : Prop :=
  ∃ δ : ℝ, |δ| ≤ u ∧ computed = exact * (1 + δ)

/-- Sequential accumulation after the first rounded product. -/
inductive DotTail (u : ℝ) : ℝ → List (ℝ × ℝ) → ℝ → Prop
  | nil (acc : ℝ) : DotTail u acc [] acc
  | cons {acc p next out : ℝ} {a b : ℝ} {xs : List (ℝ × ℝ)}
      (multiply : Rounded u (a * b) p)
      (add : Rounded u (acc + p) next)
      (rest : DotTail u next xs out) :
      DotTail u acc ((a, b) :: xs) out

/-- Empty products sum to zero; the first product initializes the accumulator.
This avoids an artificial rounding on addition to zero. -/
inductive SequentialDot (u : ℝ) : List (ℝ × ℝ) → ℝ → Prop
  | nil : SequentialDot u [] 0
  | cons {a b p out : ℝ} {xs : List (ℝ × ℝ)}
      (multiply : Rounded u (a * b) p)
      (rest : DotTail u p xs out) :
      SequentialDot u ((a, b) :: xs) out

/-- Subtraction of the empty dot product is bypassed, as in the first row
of Cholesky. All nonempty dot products are followed by a rounded subtraction. -/
def Residual (u : ℝ) (row : ℕ) (a dot out : ℝ) : Prop :=
  if row = 0 then out = a else Rounded u (a - dot) out

/-- The already computed products in the entry (i,j), in increasing k order. -/
def dotInputs {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : List (ℝ × ℝ) :=
  ((List.finRange n).filter (fun k => k < i)).map (fun k => (R k i, R k j))

/-- Write exactly one work-matrix entry. -/
def writeEntry {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (value : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun p q => if p = i ∧ q = j then value else R p q

/-- The scalar recurrence at an upper-triangular entry. A successful square
root has a nonnegative radicand; each actual division has a nonzero divisor.
No algorithmic error estimate is included in this specification. -/
def EntryComputation {n : ℕ} (u : ℝ)
    (A R : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (value : ℝ) : Prop :=
  i ≤ j ∧ ∃ dot residual : ℝ,
    SequentialDot u (dotInputs R i j) dot ∧
    Residual u i.val (A i j) dot residual ∧
    (if i = j then
      0 ≤ residual ∧ Rounded u (Real.sqrt residual) value
    else
      R i i ≠ 0 ∧ Rounded u (residual / R i i) value)

/-- Column order, with increasing row index within each column. -/
def entryOrder (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun j =>
    ((List.finRange n).filter (fun i => i ≤ j)).map (fun i => (i, j))

/-- A complete execution trace of the indicated sequence of scalar steps. -/
inductive Execute {n : ℕ} (u : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    List (Fin n × Fin n) → Matrix (Fin n) (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ → Prop
  | nil (R : Matrix (Fin n) (Fin n) ℝ) : Execute u A [] R R
  | cons {i j : Fin n} {xs : List (Fin n × Fin n)}
      {R out : Matrix (Fin n) (Fin n) ℝ} {value : ℝ}
      (entry : EntryComputation u A R i j value)
      (rest : Execute u A xs (writeEntry R i j value) out) :
      Execute u A ((i, j) :: xs) R out

/-- Successful floating-point Cholesky on the original input, including the
local no-overflow/underflow relative-error specifications. Below-diagonal
entries remain zero because execution starts at zero and writes only i ≤ j. -/
def SuccessfulCholesky {n : ℕ} (u : ℝ)
    (A Rhat : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Execute u A (entryOrder n) 0 Rhat

/-- The standard deterministic rounding constant. -/
noncomputable def gamma (m : ℕ) (u : ℝ) : ℝ := (m : ℝ) * u / (1 - (m : ℝ) * u)

/-- Entrywise absolute value, distinct from a matrix norm. -/
def entrywiseAbs {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => |M i j|

/-- The required perturbation of the original input. -/
def backwardPerturbation {n : ℕ}
    (A Rhat : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Rhat.transpose * Rhat - A

def Before {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  p.2 < q.2 ∨ p.2 = q.2 ∧ p.1 < q.1

lemma entryOrder_sorted (n : ℕ) : (entryOrder n).Pairwise Before := by
  unfold entryOrder
  rw [List.pairwise_flatMap]
  constructor
  · intro j hj
    rw [List.pairwise_map]
    apply List.Pairwise.imp (fun h => Or.inr ⟨rfl, h⟩)
    exact (List.sortedLT_finRange n).pairwise.filter _
  · apply (List.sortedLT_finRange n).pairwise.imp
    intro j k hjk p hp q hq
    simp only [List.mem_map] at hp hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    exact Or.inl hjk

lemma entryOrder_mem {n : ℕ} (i j : Fin n) : (i,j) ∈ entryOrder n ↔ i ≤ j := by
  simp [entryOrder]

lemma execute_unchanged {n : ℕ} {u : ℝ} {A R S : Matrix (Fin n) (Fin n) ℝ}
    {xs : List (Fin n × Fin n)} (h : Execute u A xs R S)
    {p q : Fin n} (hpq : (p,q) ∉ xs) : S p q = R p q := by
  induction h with
  | nil => rfl
  | @cons i j xs R out value he hr ih =>
    have hn : ¬ (p=i ∧ q=j) := by
      intro hh
      apply hpq
      simp [hh.1, hh.2]
    rw [ih (fun hm => hpq (List.mem_cons_of_mem _ hm))]
    simp [writeEntry, hn]

lemma execute_triangular {n : ℕ} {u : ℝ} {A R S : Matrix (Fin n) (Fin n) ℝ}
    {xs : List (Fin n × Fin n)} (h : Execute u A xs R S)
    (hR : ∀ i j, j < i → R i j = 0) : ∀ i j, j < i → S i j = 0 := by
  induction h with
  | nil => exact hR
  | @cons i j xs R out value he hr ih =>
    apply ih
    intro p q hpq
    have hij := he.1
    have hn : ¬ (p=i ∧ q=j) := by rintro ⟨rfl,rfl⟩; exact (not_lt_of_ge hij) hpq
    simpa [writeEntry, hn] using hR p q hpq

lemma entry_congr {n : ℕ} {u : ℝ} {A R S : Matrix (Fin n) (Fin n) ℝ}
    {i j : Fin n} {v : ℝ}
    (h : EntryComputation u A R i j v)
    (hpivot : i ≠ j → S i i = R i i)
    (hcols : ∀ k, k < i → S k i = R k i ∧ S k j = R k j) :
    EntryComputation u A S i j v := by
  have hin : dotInputs S i j = dotInputs R i j := by
    unfold dotInputs
    apply List.map_congr_left
    intro k hk
    have hk' : k < i := by simpa using (List.mem_filter.mp hk).2
    rw [(hcols k hk').1, (hcols k hk').2]
  obtain ⟨hij, d, r, hd, hr, hb⟩ := h
  refine ⟨hij, d, r, hin.symm ▸ hd, hr, ?_⟩
  by_cases heq : i=j
  · simpa [heq] using hb
  · simpa only [if_neg heq, hpivot heq] using hb

lemma execute_final_entries {n : ℕ} {u : ℝ} {A R S : Matrix (Fin n) (Fin n) ℝ}
    {xs : List (Fin n × Fin n)} (h : Execute u A xs R S)
    (hs : xs.Pairwise Before) :
    ∀ p ∈ xs, EntryComputation u A S p.1 p.2 (S p.1 p.2) := by
  induction h with
  | nil => simp
  | @cons i j xs R out value he hr ih =>
    obtain ⟨hall, htail⟩ := List.pairwise_cons.mp hs
    intro p hp
    rcases List.mem_cons.mp hp with hfirst | hrest
    · subst p
      have stable : ∀ a b, ¬ Before (i,j) (a,b) → out a b = (writeEntry R i j value) a b := by
        intro a b hn
        apply execute_unchanged hr
        intro hab
        exact hn (hall _ hab)
      have hv : out i j = value := by
        simpa [writeEntry] using stable i j (by simp [Before])
      rw [hv]
      apply entry_congr he
      · intro hij
        have hi := he.1
        have hstable := stable i i (by simp [Before]; omega)
        simpa [writeEntry, hij] using hstable
      · intro k hk
        have hi := he.1
        constructor
        · have hstable := stable k i (by simp [Before]; omega)
          simpa [writeEntry, ne_of_lt hk] using hstable
        · have hstable := stable k j (by simp [Before]; omega)
          simpa [writeEntry, ne_of_lt hk] using hstable
    · exact ih htail p hrest


open CholeskyProof

lemma rounded_error {u x y : ℝ} (h : Rounded u x y) : |y - x| ≤ u * |x| := by
  obtain ⟨δ, hδ, rfl⟩ := h
  calc
    |x * (1 + δ) - x| = |δ| * |x| := by rw [← abs_mul]; congr 1; ring
    _ ≤ u * |x| := mul_le_mul_of_nonneg_right hδ (abs_nonneg _)

lemma add_step {u acc t p a next W : ℝ} {d : ℕ}
    (hu : 0 ≤ u) (hd : 1 ≤ d) (hs : ((d+1 : ℕ) : ℝ) * u < 1)
    (hW : |t| ≤ W) (ha : |acc-t| ≤ g d u * W)
    (hp : |p-a| ≤ u * |a|) (hnext : Rounded u (acc+p) next) :
    |next-(t+a)| ≤ g (d+1) u * (W+|a|) := by
  have hs0 : (d : ℝ) * u < 1 := by
    rw [Nat.cast_add, Nat.cast_one] at hs
    linarith
  have hg := g_nonneg hu hs0
  have hug := u_le_g hu hd hs0
  have hW0 : 0 ≤ W := (abs_nonneg t).trans hW
  have hac : |acc| ≤ (1+g d u)*W := by
    have := abs_add_le (acc-t) t
    rw [sub_add_cancel] at this
    nlinarith
  have hpc : |p| ≤ (1+g d u)*|a| := by
    have := abs_add_le (p-a) a
    rw [sub_add_cancel] at this
    nlinarith [abs_nonneg a]
  have hsum : |acc+p| ≤ (1+g d u)*(W+|a|) := by
    calc
      _ ≤ |acc| + |p| := abs_add_le _ _
      _ ≤ _ := by nlinarith
  have he := rounded_error hnext
  have htri : |next-(t+a)| ≤ |next-(acc+p)| + (|acc-t| + |p-a|) := by
    calc
      _ = |(next-(acc+p)) + ((acc-t)+(p-a))| := by congr 1; ring
      _ ≤ |next-(acc+p)| + |(acc-t)+(p-a)| := abs_add_le _ _
      _ ≤ _ := by gcongr; exact abs_add_le _ _
  have hstep := g_step hu hs
  calc
    _ ≤ (g d u + u + g d u*u)*(W+|a|) := by
      nlinarith [mul_le_mul_of_nonneg_left hsum hu,
        mul_nonneg (sub_nonneg.mpr hug) (abs_nonneg a)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hstep (by positivity)

lemma dotTail_error {u acc out : ℝ} {xs : List (ℝ × ℝ)}
    (h : DotTail u acc xs out) (hu : 0 ≤ u) :
    ∀ (d : ℕ) (t W : ℝ), 1 ≤ d → |t| ≤ W → |acc-t| ≤ g d u * W →
      ((d+xs.length : ℕ) : ℝ)*u < 1 →
      |out - (t + (xs.map (fun ab => ab.1*ab.2)).sum)| ≤
        g (d+xs.length) u * (W+(xs.map (fun ab => |ab.1*ab.2|)).sum) := by
  induction h with
  | nil acc =>
      intro d t W hd hW ha hs
      simpa using ha
  | @cons acc p next out a b xs hm hadd hrest ih =>
      intro d t W hd hW ha hs
      have hs' : ((d+1 : ℕ) : ℝ)*u < 1 := by
        have hn : ((d+1 : ℕ) : ℝ) ≤ ((d+((a,b)::xs).length : ℕ) : ℝ) := by
          exact_mod_cast (show d+1 ≤ d+((a,b)::xs).length by simp)
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hn hu) hs
      have he := add_step hu hd hs' hW ha (rounded_error hm) hadd
      have ht : |t+a*b| ≤ W+|a*b| := (abs_add_le _ _).trans (by linarith)
      have hi := ih (d+1) (t+a*b) (W+|a*b|) (by omega) ht he (by
        simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs)
      simpa [List.map_cons, List.sum_cons, add_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

lemma sequentialDot_error {u out : ℝ} {xs : List (ℝ × ℝ)}
    (h : SequentialDot u xs out) (hu : 0 ≤ u)
    (hs : (xs.length : ℝ)*u < 1) :
    |out-(xs.map (fun ab => ab.1*ab.2)).sum| ≤
      g xs.length u * (xs.map (fun ab => |ab.1*ab.2|)).sum := by
  cases h with
  | nil => simp [g]
  | @cons a b p out xs hm htail =>
      have hs1 : (1 : ℝ)*u < 1 := by
        have hn : (1 : ℝ) ≤ (((a,b)::xs).length : ℝ) := by exact_mod_cast (show 1 ≤ ((a,b)::xs).length by simp)
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hn hu) hs
      have hp : |p-a*b| ≤ g 1 u * |a*b| :=
        (rounded_error hm).trans (mul_le_mul_of_nonneg_right (u_le_g (m := 1) hu (by rfl) (by simpa using hs1)) (abs_nonneg _))
      have hi := dotTail_error htail hu 1 (a*b) |a*b| (by rfl) (le_refl _) hp (by
        simpa [List.length_cons, Nat.add_comm] using hs)
      simpa [List.map_cons, List.sum_cons, Nat.add_comm] using hi


lemma envelope_mul {u x y : ℝ} {m k : ℕ}
    (hu : 0 ≤ u) (hs : ((m+k : ℕ) : ℝ)*u < 1)
    (hx : 1-(m : ℝ)*u ≤ x ∧ x ≤ 1/(1-(m : ℝ)*u))
    (hy : 1-(k : ℝ)*u ≤ y ∧ y ≤ 1/(1-(k : ℝ)*u)) :
    1-((m+k : ℕ) : ℝ)*u ≤ x*y ∧ x*y ≤ 1/(1-((m+k : ℕ) : ℝ)*u) := by
  have hm0 : 0 ≤ (m : ℝ)*u := mul_nonneg (Nat.cast_nonneg _) hu
  have hk0 : 0 ≤ (k : ℝ)*u := mul_nonneg (Nat.cast_nonneg _) hu
  have hm : 0 < 1-(m : ℝ)*u := by rw [Nat.cast_add] at hs; linarith
  have hk : 0 < 1-(k : ℝ)*u := by rw [Nat.cast_add] at hs; linarith
  have hsum : 0 < 1-((m+k : ℕ) : ℝ)*u := by linarith
  constructor
  · have hp := mul_le_mul hx.1 hy.1 (by linarith : 0 ≤ 1-(k : ℝ)*u) (by linarith : 0 ≤ x)
    rw [Nat.cast_add]
    nlinarith [mul_nonneg hm0 hk0]
  · calc
      x*y ≤ (1/(1-(m : ℝ)*u))*(1/(1-(k : ℝ)*u)) :=
        mul_le_mul hx.2 hy.2 (by linarith) (by positivity)
      _ ≤ _ := by
        rw [one_div_mul_one_div]
        apply (div_le_div_iff₀ (mul_pos hm hk) hsum).2
        rw [Nat.cast_add]
        nlinarith [mul_nonneg hm0 hk0]

lemma inverse_envelope {u δ : ℝ} (hu : 0 ≤ u) (hs : u < 1) (hδ : |δ| ≤ u) :
    1-u ≤ (1+δ)⁻¹ ∧ (1+δ)⁻¹ ≤ 1/(1-u) := by
  have hb := abs_le.mp hδ
  have hd : 0 < 1+δ := by linarith
  constructor
  · rw [inv_eq_one_div]
    apply (le_div_iff₀ hd).2
    nlinarith [sq_nonneg u]
  · rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma envelope_error {u x : ℝ} {m : ℕ} (hu : 0 ≤ u) (hs : (m : ℝ)*u < 1)
    (hx : 1-(m : ℝ)*u ≤ x ∧ x ≤ 1/(1-(m : ℝ)*u)) : |x-1| ≤ g m u := by
  have ht : 0 ≤ (m : ℝ)*u := mul_nonneg (Nat.cast_nonneg _) hu
  have hd : 0 < 1-(m : ℝ)*u := by linarith
  apply abs_le.mpr
  constructor
  · have ht' : (m : ℝ)*u ≤ g m u := by
      unfold g
      apply (le_div_iff₀ hd).2
      nlinarith [sq_nonneg ((m : ℝ)*u)]
    linarith [hx.1]
  · have hi : 1/(1-(m : ℝ)*u)-1 = g m u := by
      unfold g
      field_simp
      ring
    linarith [hx.2]

lemma inverse_two_error {u δ ε : ℝ} (hu : 0 ≤ u) (hs : (2 : ℝ)*u < 1)
    (hδ : |δ| ≤ u) (hε : |ε| ≤ u) :
    |(1+δ)⁻¹*(1+ε)⁻¹-1| ≤ g 2 u := by
  have h1 : u < 1 := by linarith
  apply envelope_error hu hs
  simpa using envelope_mul (m := 1) (k := 1) hu (by simpa using hs)
    (by simpa using inverse_envelope hu h1 hδ)
    (by simpa using inverse_envelope hu h1 hε)

lemma inverse_three_error {u δ ε ζ : ℝ} (hu : 0 ≤ u) (hs : (3 : ℝ)*u < 1)
    (hδ : |δ| ≤ u) (hε : |ε| ≤ u) (hζ : |ζ| ≤ u) :
    |((1+δ)⁻¹*(1+ε)⁻¹)*(1+ζ)⁻¹-1| ≤ g 3 u := by
  have h1 : u < 1 := by linarith
  have h2 : (2 : ℝ)*u < 1 := by linarith
  have he := envelope_mul (m := 1) (k := 1) hu (by simpa using h2)
    (by simpa using inverse_envelope hu h1 hδ)
    (by simpa using inverse_envelope hu h1 hε)
  apply envelope_error hu hs
  simpa using envelope_mul (m := 2) (k := 1) hu (by simpa using hs) he
    (by simpa using inverse_envelope hu h1 hζ)


lemma scalar_combine {G s dot P a q W : ℝ} (hG : 0 ≤ G)
    (hd : |dot-s| ≤ G*W) (hq : |q-1| ≤ G) (ha : a=dot+P*q) :
    |s+P-a| ≤ G*(W+|P|) := by
  calc
    |s+P-a| = |(s-dot)+P*(1-q)| := by rw [ha]; congr 1; ring
    _ ≤ |s-dot|+|P*(1-q)| := abs_add_le _ _
    _ = |dot-s|+|P| * |q-1| := by rw [abs_sub_comm s dot, abs_mul, abs_sub_comm 1 q]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hq (abs_nonneg P)]

lemma dotInputs_length {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (dotInputs R i j).length ≤ n := by
  simpa [dotInputs] using List.length_filter_le (fun k : Fin n => decide (k < i)) (List.finRange n)

lemma dotInputs_zero {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (hi : i.val=0) : dotInputs R i j = [] := by
  have hnone : ∀ k : Fin n, ¬ k < i := by intro k; simp only [Fin.lt_iff_val_lt_val]; omega
  simp [dotInputs, List.filter_eq_nil_iff, hnone]

lemma local_error {n : ℕ} {A R : Matrix (Fin n) (Fin n) ℝ} {u : ℝ}
    (hu : 0 ≤ u) (hs : ((n+1 : ℕ) : ℝ)*u < 1) (i j : Fin n)
    (he : EntryComputation u A R i j (R i j)) :
    |(dotInputs R i j |>.map (fun ab => ab.1*ab.2)).sum + R i i*R i j - A i j| ≤
      g (n+1) u * ((dotInputs R i j |>.map (fun ab => |ab.1*ab.2|)).sum + |R i i*R i j|) := by
  obtain ⟨hij, dot, residual, hd, hr, hb⟩ := he
  have hu1 : u < 1 := by
    have hn : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
    nlinarith [mul_le_mul_of_nonneg_right hn hu]
  have hlen := dotInputs_length R i j
  have hsmalllen : ((dotInputs R i j).length : ℝ)*u < 1 := by
    have hn : ((dotInputs R i j).length : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (show (dotInputs R i j).length ≤ n+1 by omega)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hn hu) hs
  have hderr := sequentialDot_error hd hu hsmalllen
  have hsum0 : 0 ≤ ((dotInputs R i j).map (fun ab => |ab.1*ab.2|)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _
  have hderr' : |dot-((dotInputs R i j).map (fun ab => ab.1*ab.2)).sum| ≤
      g (n+1) u * ((dotInputs R i j).map (fun ab => |ab.1*ab.2|)).sum :=
    hderr.trans (mul_le_mul_of_nonneg_right (g_mono hu (by omega) hs) hsum0)
  have hres : ∃ δ : ℝ, |δ| ≤ u ∧ residual=(A i j-dot)*(1+δ) ∧ (i.val=0 → δ=0) := by
    by_cases hi : i.val=0
    · have hz : dot=0 := by rw [dotInputs_zero R i j hi] at hd; cases hd; rfl
      refine ⟨0, by simpa using hu, ?_, fun _ => rfl⟩
      simpa [Residual, hi, hz] using hr
    · obtain ⟨δ,hδ,heq⟩ := (show Rounded u (A i j-dot) residual by simpa [Residual, hi] using hr)
      exact ⟨δ,hδ,heq,fun hh => (hi hh).elim⟩
  obtain ⟨δ,hδ,hr,hrzero⟩ := hres
  have hδpos : 0 < 1+δ := by have := (abs_le.mp hδ).1; linarith
  have h2small : (2 : ℝ)*u < 1 := by
    have hn : (2 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n+1 by have := i.isLt; omega)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hn hu) hs
  by_cases heq : i=j
  · subst j
    simp only [if_pos rfl] at hb
    obtain ⟨hr0, ε, hε, hv⟩ := hb
    have hεpos : 0 < 1+ε := by have := (abs_le.mp hε).1; linarith
    have hv2 : R i i ^ 2 = residual*(1+ε)^2 := by rw [hv, mul_pow, Real.sq_sqrt hr0]
    by_cases hi : i.val=0
    · have hδzero := hrzero hi
      subst δ
      have ha : A i i = dot + (R i i*R i i)*((1+ε)⁻¹*(1+ε)⁻¹) := by
        rw [← sq, hv2, hr]
        field_simp
        <;> ring
      apply scalar_combine (g_nonneg hu hs) hderr' _ ha
      exact (inverse_two_error hu h2small hε hε).trans (g_mono hu (by have := i.isLt; omega) hs)
    · have h3small : (3 : ℝ)*u < 1 := by
        have hn : (3 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ n+1 by have := i.isLt; omega)
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hn hu) hs
      have ha : A i i = dot + (R i i*R i i)*(((1+δ)⁻¹*(1+ε)⁻¹)*(1+ε)⁻¹) := by
        rw [← sq, hv2, hr]
        field_simp
        <;> ring
      apply scalar_combine (g_nonneg hu hs) hderr' _ ha
      exact (inverse_three_error hu h3small hδ hε hε).trans (g_mono hu (by have := i.isLt; omega) hs)
  · simp only [if_neg heq] at hb
    obtain ⟨hpivot, ε, hε, hv⟩ := hb
    have hεpos : 0 < 1+ε := by have := (abs_le.mp hε).1; linarith
    have ha : A i j = dot + (R i i*R i j)*((1+δ)⁻¹*(1+ε)⁻¹) := by
      rw [hv, hr]
      field_simp
      <;> ring
    apply scalar_combine (g_nonneg hu hs) hderr' _ ha
    exact (inverse_two_error hu h2small hδ hε).trans (g_mono hu (by have := i.isLt; omega) hs)


lemma sum_filter_map {α : Type*} (l : List α) (p : α → Prop) [DecidablePred p] (f : α → ℝ) :
    ((l.filter (fun x => decide (p x))).map f).sum = (l.map (fun x => if p x then f x else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases ha : p a <;> simp [ha, ih]

lemma sum_cut {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hf : ∀ k, i < k → f k=0) :
    ∑ k, f k = (((List.finRange n).filter (fun k => k < i)).map f).sum + f i := by
  rw [sum_filter_map]
  simp only [List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_apply, id_eq]
  calc
    ∑ k, f k = ∑ k, ((if k < i then f k else 0) + (if k=i then f i else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hki : k < i
      · simp [hki, ne_of_lt hki]
      · by_cases heq : k=i
        · simp [heq]
        · have hz := hf k (lt_of_le_of_ne (le_of_not_gt hki) (Ne.symm heq))
          simp [hki, heq, hz]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

lemma gram_cut {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (ht : ∀ i j, j < i → R i j=0) (i j : Fin n) :
    (R.transpose*R) i j = ((dotInputs R i j).map (fun ab => ab.1*ab.2)).sum + R i i*R i j := by
  simpa [Matrix.mul_apply, Matrix.transpose_apply, dotInputs, List.map_map, Function.comp_def]
    using sum_cut i (fun k => R k i*R k j) (by intro k hk; simp [ht k i hk])

lemma abs_gram_cut {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (ht : ∀ i j, j < i → R i j=0) (i j : Fin n) :
    (entrywiseAbs R.transpose*entrywiseAbs R) i j =
      ((dotInputs R i j).map (fun ab => |ab.1*ab.2|)).sum + |R i i*R i j| := by
  simpa [Matrix.mul_apply, Matrix.transpose_apply, entrywiseAbs, dotInputs, List.map_map, Function.comp_def, abs_mul]
    using sum_cut i (fun k => |R k i| * |R k j|) (by intro k hk; simp [ht k i hk])


/-- The complete componentwise Cholesky backward-error theorem. All dimensions,
including zero, and zero unit roundoff are allowed. Positive definiteness is
retained explicitly, even though successful execution supplies the local
conditions used in the backward-error argument. -/
theorem cholesky_factorization
    {n : ℕ} (A Rhat : Matrix (Fin n) (Fin n) ℝ) (u : ℝ)
    (hSymm : A.IsSymm) (hPosDef : A.PosDef)
    (hu : 0 ≤ u) (hsmall : ((n + 1 : ℕ) : ℝ) * u < 1)
    (hcomputed : SuccessfulCholesky u A Rhat) :
    ∃ ΔA : Matrix (Fin n) (Fin n) ℝ,
      ΔA = backwardPerturbation A Rhat ∧
      ΔA.IsSymm ∧
      Rhat.transpose * Rhat = A + ΔA ∧
      ∀ i j : Fin n,
        |ΔA i j| ≤ gamma (n + 1) u *
          (entrywiseAbs Rhat.transpose * entrywiseAbs Rhat) i j := by
  have ht : ∀ i j, j < i → Rhat i j = 0 :=
    execute_triangular hcomputed (by intros; rfl)
  have he : ∀ i j, i ≤ j → EntryComputation u A Rhat i j (Rhat i j) := by
    intro i j hij
    exact execute_final_entries hcomputed (entryOrder_sorted n) (i,j) ((entryOrder_mem i j).mpr hij)
  have hGram : (Rhat.transpose*Rhat).IsSymm := Matrix.isSymm_transpose_mul_self Rhat
  have hAbsGram : (entrywiseAbs Rhat.transpose*entrywiseAbs Rhat).IsSymm :=
    Matrix.isSymm_transpose_mul_self (entrywiseAbs Rhat)
  have hDelta : (backwardPerturbation A Rhat).IsSymm := hGram.sub hSymm
  refine ⟨backwardPerturbation A Rhat, rfl, hDelta, ?_, ?_⟩
  · unfold backwardPerturbation
    abel
  · have upper : ∀ i j, i ≤ j →
        |backwardPerturbation A Rhat i j| ≤ gamma (n+1) u *
          (entrywiseAbs Rhat.transpose*entrywiseAbs Rhat) i j := by
      intro i j hij
      have hlocal := local_error hu hsmall i j (he i j hij)
      rw [← gram_cut Rhat ht i j, ← abs_gram_cut Rhat ht i j] at hlocal
      exact hlocal
    intro i j
    by_cases hij : i ≤ j
    · exact upper i j hij
    · rw [hDelta.apply j i, hAbsGram.apply j i]
      exact upper j i (le_of_not_ge hij)

end Cholesky
