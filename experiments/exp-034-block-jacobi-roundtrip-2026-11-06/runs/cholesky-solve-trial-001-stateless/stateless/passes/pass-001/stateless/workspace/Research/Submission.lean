import Mathlib

/-!
Formal statement of `theorem:cholesky_solve` in the supplied source.

The execution relations below record elementary operations, not backward-error
estimates. Indices are zero based. Equations for Cholesky entries are in column
order, forward substitution in increasing row order, and backward substitution
in decreasing row order; every right-hand-side entry is already available.

No overflow/underflow is expressed by the validity of the relative-error model
at every operation actually executed. Square root uses the same relative-error
model (the usual correctly rounded square-root semantics). This is an explicit
modeling completion: the source's displayed model lists only +,-,*,/ although
its Cholesky theorem and proof also use rounded square roots. Without a model
for square root that theorem does not follow from the four-operation model.

Statement revision record: no /spec/feedback.json was supplied. No prior Lean
statement was supplied. Both requested constants and the original input/output
linkage are retained; no factorization or solve error bound is a hypothesis.
-/

namespace Research.CholeskySolve

noncomputable section

/-- The standard accumulated relative error constant. -/
def gamma (u : ℝ) (k : ℕ) : ℝ := (k : ℝ) * u / (1 - (k : ℝ) * u)

/-- Absolute value is entrywise, not a matrix norm or spectral absolute value. -/
def entrywiseAbs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => |A i j|

/-- A valid individual rounding event in the absence of overflow/underflow.
The exact input is rounded once, with an operation-specific relative error. -/
def Rounded (u exact computed : ℝ) : Prop :=
  ∃ δ : ℝ, |δ| ≤ u ∧ computed = exact * (1 + δ)

/-- Sequential dot product: each product is rounded and the products are added
from left to right. The first product is not added to an artificial zero. -/
inductive DotTrace (u : ℝ) : List (ℝ × ℝ) → ℝ → Prop
  | nil : DotTrace u [] 0
  | single (a b p : ℝ) (hp : Rounded u (a * b) p) :
      DotTrace u [(a, b)] p
  | snoc (xs : List (ℝ × ℝ)) (a b s p t : ℝ)
      (hne : xs ≠ []) (hs : DotTrace u xs s)
      (hp : Rounded u (a * b) p) (ht : Rounded u (s + p) t) :
      DotTrace u (xs ++ [(a, b)]) t

/-- Rounded subtraction of a dot product. An empty sum requires no arithmetic. -/
def ResidualTrace (u c : ℝ) (terms : List (ℝ × ℝ)) (s : ℝ) : Prop :=
  if terms = [] then s = c
  else ∃ p : ℝ, DotTrace u terms p ∧ Rounded u (c - p) s

/-- A substitution/off-diagonal Cholesky update, including its division. -/
def UpdateTrace (u c d : ℝ) (terms : List (ℝ × ℝ)) (z : ℝ) : Prop :=
  d ≠ 0 ∧ ∃ s : ℝ, ResidualTrace u c terms s ∧ Rounded u (s / d) z

/-- A successful diagonal update, including a rounded square root.
Positive radicand and output express successful factorization. -/
def DiagonalTrace (u c : ℝ) (terms : List (ℝ × ℝ)) (z : ℝ) : Prop :=
  ∃ s : ℝ, ResidualTrace u c terms s ∧ 0 < s ∧
    Rounded u (Real.sqrt s) z ∧ 0 < z

/-- Products used in the entry (i,j) Cholesky update, in increasing k order. -/
def factorTerms {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    List (ℝ × ℝ) :=
  ((List.finRange n).filter (fun k => k < i)).map (fun k => (R k i, R k j))

/-- Products already available to row i of forward substitution. -/
def forwardTerms {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin n → ℝ) (i : Fin n) : List (ℝ × ℝ) :=
  ((List.finRange n).filter (fun k => k < i)).map (fun k => (T i k, y k))

/-- Products already available to row i of backward substitution.
The dot product is accumulated in increasing column order. -/
def backwardTerms {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (i : Fin n) : List (ℝ × ℝ) :=
  ((List.finRange n).filter (fun k => i < k)).map (fun k => (T i k, x k))

/-- Operation-level trace of the standard upper-triangular Cholesky algorithm.
All entry equations are acyclic and use only earlier entries in column order. -/
structure FactorTrace {n : ℕ} (u : ℝ) (A R : Matrix (Fin n) (Fin n) ℝ) : Prop where
  upper : ∀ i j, j < i → R i j = 0
  diagonal : ∀ j, DiagonalTrace u (A j j) (factorTerms R j j) (R j j)
  offDiagonal : ∀ i j, i < j →
    UpdateTrace u (A i j) (R i i) (factorTerms R i j) (R i j)

/-- Forward substitution with all intermediate arithmetic recorded. -/
def ForwardTrace {n : ℕ} (u : ℝ) (T : Matrix (Fin n) (Fin n) ℝ)
    (b y : Fin n → ℝ) : Prop :=
  (∀ i j, i < j → T i j = 0) ∧
  ∀ i, UpdateTrace u (b i) (T i i) (forwardTerms T y i) (y i)

/-- Backward substitution with all intermediate arithmetic recorded. -/
def BackwardTrace {n : ℕ} (u : ℝ) (T : Matrix (Fin n) (Fin n) ℝ)
    (b x : Fin n → ℝ) : Prop :=
  (∀ i j, j < i → T i j = 0) ∧
  ∀ i, UpdateTrace u (b i) (T i i) (backwardTerms T x i) (x i)

/-- A successful Cholesky solve on the original inputs A,b: the intermediate
right-hand side is the actual output of the forward solve with R transpose. -/
structure SolveTrace {n : ℕ} (u : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (R : Matrix (Fin n) (Fin n) ℝ)
    (y x : Fin n → ℝ) : Prop where
  factor : FactorTrace u A R
  forward : ForwardTrace u R.transpose b y
  backward : BackwardTrace u R y x

/-- The factorization perturbation, defined from the computed factor. -/
def factorPerturbation {n : ℕ} (A R : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := R.transpose * R - A

/-- The full perturbation assembled from factorization and substitution errors.
EL perturbs R transpose and EU perturbs R, so multiplication order matters. -/
def solvePerturbation {n : ℕ} (A R EL EU : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  factorPerturbation A R + R.transpose * EU + EL * R + EL * EU

lemma gamma_nonneg {u : ℝ} (hu : 0 ≤ u) {k : ℕ} (hk : (k : ℝ) * u < 1) :
    0 ≤ gamma u k := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

lemma gamma_mono {u : ℝ} (hu : 0 ≤ u) {k l : ℕ} (hkl : k ≤ l)
    (hl : (l : ℝ) * u < 1) : gamma u k ≤ gamma u l := by
  have hku : (k : ℝ) * u ≤ (l : ℝ) * u := mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) hu
  unfold gamma
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith

lemma gamma_comp {u : ℝ} (hu : 0 ≤ u) {k l : ℕ}
    (h : ((k + l : ℕ) : ℝ) * u < 1) :
    gamma u k + gamma u l + gamma u k * gamma u l ≤ gamma u (k + l) := by
  have hk : (k : ℝ) * u < 1 := by
    have : (0 : ℝ) ≤ (l : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
    push_cast at h
    nlinarith
  have hl : (l : ℝ) * u < 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
    push_cast at h
    nlinarith
  have hk0 : 0 < 1-(k:ℝ)*u := by linarith
  have hl0 : 0 < 1-(l:ℝ)*u := by linarith
  have hs0 : 0 < 1-((k+l:ℕ):ℝ)*u := by linarith
  have eqg (m : ℕ) (hm : 0 < 1-(m:ℝ)*u) :
      1 + gamma u m = 1 / (1-(m:ℝ)*u) := by
    unfold gamma
    field_simp
    <;> ring
  have hm : (1 + gamma u k)*(1+gamma u l) ≤ 1+gamma u (k+l) := by
    rw [eqg k hk0, eqg l hl0, eqg (k+l) hs0, ← mul_div_mul_comm]
    apply (div_le_div_iff₀ (mul_pos hk0 hl0) hs0).2
    simp only [one_mul, mul_one, Nat.cast_add]
    nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hu) (mul_nonneg (Nat.cast_nonneg l) hu)]
  nlinarith

lemma relative_mul {u p q : ℝ} {k l : ℕ} (hu : 0 ≤ u)
    (h : ((k+l : ℕ) : ℝ) * u < 1)
    (hp : |p - 1| ≤ gamma u k) (hq : |q - 1| ≤ gamma u l) :
    |p*q - 1| ≤ gamma u (k+l) := by
  have hk : (k : ℝ) * u < 1 := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right k l) hu) h
  have hl : (l : ℝ) * u < 1 := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_left l k) hu) h
  calc
    |p*q-1| = |(p-1) + (q-1) + (p-1)*(q-1)| := by congr 1; ring
    _ ≤ |p-1| + |q-1| + |p-1| *|q-1| := by
      simpa [abs_mul] using (abs_add_three (p-1) (q-1) ((p-1)*(q-1)))
    _ ≤ gamma u k + gamma u l + gamma u k * gamma u l :=
      add_le_add (add_le_add hp hq) (mul_le_mul hp hq (abs_nonneg _) (gamma_nonneg hu hk))
    _ ≤ gamma u (k+l) := gamma_comp hu h

lemma rounding_factors {u δ : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) (hδ : |δ| ≤ u) :
    0 < 1 + δ ∧ |(1 + δ) - 1| ≤ gamma u 1 ∧ |(1 + δ)⁻¹ - 1| ≤ gamma u 1 := by
  have hd := (abs_le.mp hδ)
  have hp : 0 < 1 + δ := by linarith
  have hg : u ≤ gamma u 1 := by
    simp only [gamma, Nat.cast_one, one_mul]
    apply (le_div_iff₀ (by linarith : 0 < 1-u)).2
    nlinarith [sq_nonneg u]
  refine ⟨hp, by simpa using hδ.trans hg, ?_⟩
  have he : (1 + δ)⁻¹ - 1 = -δ / (1+δ) := by field_simp; ring
  rw [he, abs_div, abs_neg, abs_of_pos hp]
  simp only [gamma, Nat.cast_one, one_mul]
  apply (div_le_div_iff₀ hp (by linarith)).2
  have hmul := mul_le_mul_of_nonneg_right hδ (show 0 ≤ 1-u by linarith)
  nlinarith

/-- Exact and absolute sums of the products in a dot-product trace. -/
def dotExact (ts : List (ℝ × ℝ)) : ℝ := (ts.map (fun p => p.1*p.2)).sum
def dotSize (ts : List (ℝ × ℝ)) : ℝ := (ts.map (fun p => |p.1*p.2|)).sum

lemma dotSize_nonneg (ts : List (ℝ × ℝ)) : 0 ≤ dotSize ts := by
  unfold dotSize
  exact List.sum_nonneg (by intro a ha; obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha; exact abs_nonneg _)

lemma dotExact_abs (ts : List (ℝ × ℝ)) : |dotExact ts| ≤ dotSize ts := by
  induction ts with
  | nil => simp [dotExact, dotSize]
  | cons p ts ih =>
    simp only [dotExact, dotSize, List.map_cons, List.sum_cons] at *
    exact (abs_add_le _ _).trans (add_le_add_right ih _)

lemma dot_error {u : ℝ} (hu : 0 ≤ u) {ts : List (ℝ × ℝ)} {s : ℝ}
    (ht : DotTrace u ts s) (hsmall : (ts.length : ℝ)*u < 1) :
    |s - dotExact ts| ≤ gamma u ts.length * dotSize ts := by
  induction ht with
  | nil => simp [dotExact, dotSize]
  | single a b p hp =>
    obtain ⟨δ, hd, rfl⟩ := hp
    have hu1 : u < 1 := by simpa using hsmall
    have hf := (rounding_factors hu hu1 hd).2.1
    simp only [List.length_singleton, dotExact, dotSize, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    have he : a*b*(1+δ)-a*b = (1+δ-1)*(a*b) := by ring
    rw [he, abs_mul]
    exact mul_le_mul_of_nonneg_right hf (abs_nonneg _)
  | snoc xs a b s p t hne hs hp ht ih =>
    have hlen : (xs ++ [(a,b)]).length = xs.length + 1 := by simp
    rw [hlen] at hsmall ⊢
    have hx : (xs.length : ℝ)*u < 1 := lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ xs.length) hu) hsmall
    have hu1 : u < 1 := lt_of_le_of_lt
      (by have : (1:ℝ) ≤ ((xs.length+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
          simpa using mul_le_mul_of_nonneg_right this hu) hsmall
    have ih := ih hx
    obtain ⟨δ, hd, rfl⟩ := hp
    obtain ⟨ε, he, rfl⟩ := ht
    have hd1 := (rounding_factors hu hu1 hd).2.1
    have he1 := (rounding_factors hu hu1 he).2.1
    have htwo : 2 ≤ xs.length+1 := by
      have : 0 < xs.length := List.length_pos_iff.mpr hne
      omega
    have h2 : (2:ℝ)*u < 1 := lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by exact_mod_cast htwo) hu) hsmall
    have hde := relative_mul hu h2 hd1 he1
    have hprod := gamma_comp hu (k := xs.length) (l := 1) hsmall
    have hg1 := gamma_nonneg (k := 1) hu (by simpa using hu1)
    have hgm := gamma_nonneg hu hx
    have hg2 := gamma_mono hu htwo hsmall
    have hexp : (s+a*b*(1+δ))*(1+ε) - (dotExact xs+a*b) =
        (s-dotExact xs)*(1+ε) + dotExact xs*((1+ε)-1) +
          a*b*((1+δ)*(1+ε)-1) := by ring
    simp only [dotExact, dotSize, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    change |(s+a*b*(1+δ))*(1+ε) - (dotExact xs+a*b)| ≤ _
    rw [hexp]
    have hab : |1+ε| ≤ 1+gamma u 1 := by
      calc |1+ε| = |1+((1+ε)-1)| := by congr 1; ring
           _ ≤ |(1:ℝ)| + |(1+ε)-1| := abs_add_le _ _
           _ ≤ 1+gamma u 1 := by simpa using add_le_add_left he1 1
    calc
      _ ≤ |s-dotExact xs| *|1+ε| + |dotExact xs| *|(1+ε)-1| +
          |a*b| *|(1+δ)*(1+ε)-1| := by simpa [abs_mul] using (abs_add_three ((s-dotExact xs)*(1+ε)) (dotExact xs*((1+ε)-1)) (a*b*((1+δ)*(1+ε)-1)))
      _ ≤ (gamma u xs.length * dotSize xs)*(1+gamma u 1) +
          dotSize xs * gamma u 1 + |a*b| * gamma u 2 := by
        exact add_le_add (add_le_add (mul_le_mul ih hab (abs_nonneg _) (mul_nonneg hgm (dotSize_nonneg _))) (mul_le_mul (dotExact_abs _) he1 (abs_nonneg _) (dotSize_nonneg _))) (mul_le_mul_of_nonneg_left hde (abs_nonneg _))
      _ ≤ gamma u (xs.length+1) * (dotSize xs + |a*b|) := by
        have hleft := mul_le_mul_of_nonneg_right hprod (dotSize_nonneg xs)
        have hright := mul_le_mul_of_nonneg_right hg2 (abs_nonneg (a*b))
        nlinarith

lemma residual_inverse {u c s : ℝ} {ts : List (ℝ × ℝ)}
    (hu : 0 ≤ u) (hu1 : u < 1) (ht : ResidualTrace u c ts s) :
    ∃ p q : ℝ, DotTrace u ts p ∧ c = p+s*q ∧
      (if ts = [] then q = 1 else |q-1| ≤ gamma u 1) := by
  unfold ResidualTrace at ht
  split_ifs at ht with h
  · subst ts
    exact ⟨0, 1, DotTrace.nil, by simpa using ht.symm, rfl⟩
  · obtain ⟨p, hp, δ, hd, hs⟩ := ht
    have hf := rounding_factors hu hu1 hd
    refine ⟨p, (1+δ)⁻¹, hp, ?_, by simpa [h] using hf.2.2⟩
    rw [hs]
    field_simp [ne_of_gt hf.1]
    <;> nlinarith

lemma update_error {u c d z : ℝ} {ts : List (ℝ × ℝ)} {K : ℕ}
    (hu : 0 ≤ u) (hK : (K:ℝ)*u < 1)
    (hlen : ts.length ≤ K) (hcount : if ts = [] then 1 ≤ K else 2 ≤ K)
    (ht : UpdateTrace u c d ts z) :
    |dotExact ts + d*z - c| ≤ gamma u K * (dotSize ts + |d*z|) := by
  have h1 : 1 ≤ K := by split_ifs at hcount <;> omega
  have hu1 : u < 1 := lt_of_le_of_lt
    (by simpa using mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ (K:ℝ) by exact_mod_cast h1) hu) hK
  obtain ⟨hd, s, hs, δ, hδ, hz⟩ := ht
  obtain ⟨p,q,hp,hc,hq⟩ := residual_inverse hu hu1 hs
  have hδf := rounding_factors hu hu1 hδ
  have hdz : d*z*(1+δ)⁻¹ = s := by rw [hz]; field_simp [hd, ne_of_gt hδf.1]; <;> ring
  have hinv : |(1+δ)⁻¹*q-1| ≤ gamma u K := by
    by_cases he : ts = []
    · rw [if_pos he] at hq hcount
      rw [hq, mul_one]
      exact hδf.2.2.trans (gamma_mono hu hcount hK)
    · rw [if_neg he] at hq hcount
      have h2 : (2:ℝ)*u < 1 := lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hu) hK
      exact (relative_mul hu h2 hδf.2.2 hq).trans (gamma_mono hu hcount hK)
  have hdot := (dot_error hu hp (lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hu) hK)).trans
    (mul_le_mul_of_nonneg_right (gamma_mono hu hlen hK) (dotSize_nonneg ts))
  have heq : dotExact ts+d*z-c = (dotExact ts-p) + d*z*(1-(1+δ)⁻¹*q) := by
    rw [hc, ← hdz]; ring
  calc
    _ = |(dotExact ts-p) + d*z*(1-(1+δ)⁻¹*q)| := by congr 1 <;> linarith [heq]
    _ ≤ |dotExact ts-p| + |d*z| *|1-(1+δ)⁻¹*q| := by simpa [abs_mul] using abs_add_le (dotExact ts-p) (d*z*(1-(1+δ)⁻¹*q))
    _ ≤ gamma u K * dotSize ts + |d*z| * gamma u K := by
      apply add_le_add
      · simpa [abs_sub_comm] using hdot
      · exact mul_le_mul_of_nonneg_left (by simpa [abs_sub_comm] using hinv) (abs_nonneg _)
    _ = _ := by ring

lemma diagonal_error {u c z : ℝ} {ts : List (ℝ × ℝ)} {K : ℕ}
    (hu : 0 ≤ u) (hK : (K:ℝ)*u < 1)
    (hlen : ts.length ≤ K) (hcount : if ts = [] then 2 ≤ K else 3 ≤ K)
    (ht : DiagonalTrace u c ts z) :
    |dotExact ts + z*z - c| ≤ gamma u K * (dotSize ts + |z*z|) := by
  have h2 : 2 ≤ K := by split_ifs at hcount <;> omega
  have hu1 : u < 1 := lt_of_le_of_lt
    (by simpa using mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ (K:ℝ) by exact_mod_cast (by omega : 1 ≤ K)) hu) hK
  obtain ⟨s, hs, hspos, hround, hzpos⟩ := ht
  obtain ⟨δ, hδ, hz⟩ := hround
  obtain ⟨p,q,hp,hc,hq⟩ := residual_inverse hu hu1 hs
  have hf := rounding_factors hu hu1 hδ
  have hK2 : (2:ℝ)*u < 1 := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast h2) hu) hK
  have hf2 := relative_mul hu hK2 hf.2.2 hf.2.2
  have hzz : z*z*((1+δ)⁻¹*(1+δ)⁻¹) = s := by
    rw [hz]
    have hsq := Real.sq_sqrt (le_of_lt hspos)
    field_simp [ne_of_gt hf.1]
    <;> nlinarith
  have hinv : |((1+δ)⁻¹*(1+δ)⁻¹)*q-1| ≤ gamma u K := by
    by_cases he : ts = []
    · rw [if_pos he] at hq hcount
      rw [hq, mul_one]
      exact hf2.trans (gamma_mono hu hcount hK)
    · rw [if_neg he] at hq hcount
      have h3 : (3:ℝ)*u < 1 := lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hu) hK
      exact (relative_mul hu h3 hf2 hq).trans (gamma_mono hu hcount hK)
  have hdot := (dot_error hu hp (lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hu) hK)).trans
    (mul_le_mul_of_nonneg_right (gamma_mono hu hlen hK) (dotSize_nonneg ts))
  have heq : dotExact ts+z*z-c = (dotExact ts-p) + z*z*(1-((1+δ)⁻¹*(1+δ)⁻¹)*q) := by
    rw [hc, ← hzz]; ring
  calc
    _ = |(dotExact ts-p) + z*z*(1-((1+δ)⁻¹*(1+δ)⁻¹)*q)| := by congr 1 <;> linarith [heq]
    _ ≤ |dotExact ts-p| + |z*z| *|1-((1+δ)⁻¹*(1+δ)⁻¹)*q| := by simpa [abs_mul] using abs_add_le (dotExact ts-p) (z*z*(1-((1+δ)⁻¹*(1+δ)⁻¹)*q))
    _ ≤ gamma u K * dotSize ts + |z*z| * gamma u K := by
      apply add_le_add
      · simpa [abs_sub_comm] using hdot
      · exact mul_le_mul_of_nonneg_left (by simpa [abs_sub_comm] using hinv) (abs_nonneg _)
    _ = _ := by ring

lemma filtered_sum {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (f : Fin n → ℝ) :
    ((((List.finRange n).filter (fun k => decide (p k))).map f).sum) =
      ∑ k, if p k then f k else 0 := by
  rw [← List.sum_toFinset f ((List.nodup_finRange n).filter _)]
  simp [List.toFinset_filter, Finset.sum_filter]

lemma products_exact {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (a b : Fin n → ℝ) :
    dotExact (((List.finRange n).filter (fun k => decide (p k))).map (fun k => (a k,b k))) =
      ∑ k, if p k then a k*b k else 0 := by
  simp only [dotExact, List.map_map, Function.comp_def]
  exact filtered_sum p _

lemma products_size {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (a b : Fin n → ℝ) :
    dotSize (((List.finRange n).filter (fun k => decide (p k))).map (fun k => (a k,b k))) =
      ∑ k, if p k then |a k*b k| else 0 := by
  simp only [dotSize, List.map_map, Function.comp_def]
  exact filtered_sum p _

lemma products_length {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (a b : Fin n → ℝ) :
    (((List.finRange n).filter (fun k => decide (p k))).map (fun k => (a k,b k))).length ≤ n := by
  simpa using List.length_filter_le (fun k => decide (p k)) (List.finRange n)

lemma products_nonempty {n : ℕ} (i : Fin n) (p : Fin n → Prop) [DecidablePred p]
    (hpi : ¬p i) (a b : Fin n → ℝ)
    (h : (((List.finRange n).filter (fun k => decide (p k))).map (fun k => (a k,b k))) ≠ []) :
    2 ≤ n := by
  by_contra hn
  have he : ∀ k : Fin n, k = i := by intro k; apply Fin.ext; have := k.isLt; have := i.isLt; omega
  apply h
  simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro k hk
  simp [he k, hpi]

lemma sum_split {n : ℕ} (i : Fin n) (p : Fin n → Prop) [DecidablePred p]
    (hpi : ¬p i) (f : Fin n → ℝ) (hf : ∀ k, k ≠ i → ¬p k → f k = 0) :
    (∑ k, if p k then f k else 0) + f i = ∑ k, f k := by
  calc
    _ = ∑ k, ((if p k then f k else 0) + if k=i then f i else 0) := by
      rw [Finset.sum_add_distrib]; simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hki : k=i
      · subst k; simp [hpi]
      · by_cases hp : p k
        · simp [hp,hki]
        · simp [hp,hki,hf k hki hp]

lemma forward_row {n : ℕ} {u : ℝ} {T : Matrix (Fin n) (Fin n) ℝ} {b x : Fin n → ℝ}
    (hu : 0 ≤ u) (hn : (n:ℝ)*u < 1) (ht : ForwardTrace u T b x) (i : Fin n) :
    |T.mulVec x i - b i| ≤ gamma u n * ∑ k, |T i k*x k| := by
  have hcount : if forwardTerms T x i = [] then 1 ≤ n else 2 ≤ n := by
    split_ifs with he
    · have := i.isLt; omega
    · exact products_nonempty i (fun k => k < i) (lt_irrefl i) _ _ he
  have herr := update_error hu hn (products_length (fun k => k < i) (T i) x) hcount (ht.2 i)
  have hex : dotExact (forwardTerms T x i) + T i i*x i = T.mulVec x i := by
    rw [forwardTerms, products_exact]
    apply sum_split i (fun k => k < i) (lt_irrefl i) _
    intro k hki hk
    have hik : i < k := lt_of_le_of_ne (le_of_not_gt hk) (Ne.symm hki)
    simp [ht.1 i k hik]
  have hab : dotSize (forwardTerms T x i) + |T i i*x i| = ∑ k, |T i k*x k| := by
    rw [forwardTerms, products_size]
    apply sum_split i (fun k => k < i) (lt_irrefl i) _
    intro k hki hk
    have hik : i < k := lt_of_le_of_ne (le_of_not_gt hk) (Ne.symm hki)
    simp [ht.1 i k hik]
  change |dotExact (forwardTerms T x i) + T i i*x i-b i| ≤ gamma u n * (dotSize (forwardTerms T x i) + |T i i*x i|) at herr
  rw [hex, hab] at herr
  exact herr

lemma backward_row {n : ℕ} {u : ℝ} {T : Matrix (Fin n) (Fin n) ℝ} {b x : Fin n → ℝ}
    (hu : 0 ≤ u) (hn : (n:ℝ)*u < 1) (ht : BackwardTrace u T b x) (i : Fin n) :
    |T.mulVec x i - b i| ≤ gamma u n * ∑ k, |T i k*x k| := by
  have hcount : if backwardTerms T x i = [] then 1 ≤ n else 2 ≤ n := by
    split_ifs with he
    · have := i.isLt; omega
    · exact products_nonempty i (fun k => i < k) (lt_irrefl i) _ _ he
  have herr := update_error hu hn (products_length (fun k => i < k) (T i) x) hcount (ht.2 i)
  have hex : dotExact (backwardTerms T x i) + T i i*x i = T.mulVec x i := by
    rw [backwardTerms, products_exact]
    apply sum_split i (fun k => i < k) (lt_irrefl i) _
    intro k hki hk
    have hki' : k < i := lt_of_le_of_ne (le_of_not_gt hk) hki
    simp [ht.1 i k hki']
  have hab : dotSize (backwardTerms T x i) + |T i i*x i| = ∑ k, |T i k*x k| := by
    rw [backwardTerms, products_size]
    apply sum_split i (fun k => i < k) (lt_irrefl i) _
    intro k hki hk
    have hki' : k < i := lt_of_le_of_ne (le_of_not_gt hk) hki
    simp [ht.1 i k hki']
  change |dotExact (backwardTerms T x i) + T i i*x i-b i| ≤ gamma u n * (dotSize (backwardTerms T x i) + |T i i*x i|) at herr
  rw [hex, hab] at herr
  exact herr

lemma factor_sums {n : ℕ} {u : ℝ} {A R : Matrix (Fin n) (Fin n) ℝ}
    (ht : FactorTrace u A R) (i j : Fin n) :
    dotExact (factorTerms R i j) + R i i*R i j = (R.transpose*R) i j ∧
    dotSize (factorTerms R i j) + |R i i*R i j| =
      (entrywiseAbs R.transpose*entrywiseAbs R) i j := by
  constructor
  · rw [factorTerms, products_exact]
    apply sum_split i (fun k => k < i) (lt_irrefl i) _
    intro k hki hk
    have hik : i < k := lt_of_le_of_ne (le_of_not_gt hk) (Ne.symm hki)
    simp [ht.upper k i hik]
  · rw [factorTerms, products_size]
    change (∑ k, if k < i then |R k i*R k j| else 0) + |R i i*R i j| =
      ∑ k, |R k i| *|R k j|
    simp only [← abs_mul]
    apply sum_split i (fun k => k < i) (lt_irrefl i) _
    intro k hki hk
    have hik : i < k := lt_of_le_of_ne (le_of_not_gt hk) (Ne.symm hki)
    simp [ht.upper k i hik]

lemma factor_bound {n : ℕ} {u : ℝ} {A R : Matrix (Fin n) (Fin n) ℝ}
    (hu : 0 ≤ u) (hn : ((n+1:ℕ):ℝ)*u < 1) (hSymm : A.transpose = A)
    (ht : FactorTrace u A R) :
    ∀ i j, |factorPerturbation A R i j| ≤ gamma u (n+1) *
      (entrywiseAbs R.transpose*entrywiseAbs R) i j := by
  have hup (i j : Fin n) (hij : i ≤ j) :
      |(R.transpose*R) i j-A i j| ≤ gamma u (n+1) *
        (entrywiseAbs R.transpose*entrywiseAbs R) i j := by
    have hlen : (factorTerms R i j).length ≤ n+1 :=
      (products_length (fun k => k < i) (fun k => R k i) (fun k => R k j)).trans (Nat.le_succ n)
    by_cases he : i=j
    · subst j
      have hcount : if factorTerms R i i = [] then 2 ≤ n+1 else 3 ≤ n+1 := by
        split_ifs with hh
        · have := i.isLt; omega
        · have := products_nonempty i (fun k => k < i) (lt_irrefl i) (fun k => R k i) (fun k => R k i) hh
          omega
      have hb := diagonal_error hu hn hlen hcount (ht.diagonal i)
      simpa only [(factor_sums ht i i).1, (factor_sums ht i i).2] using hb
    · have hcount : if factorTerms R i j = [] then 1 ≤ n+1 else 2 ≤ n+1 := by
        split_ifs <;> have := i.isLt <;> omega
      have hb := update_error hu hn hlen hcount (ht.offDiagonal i j (lt_of_le_of_ne hij he))
      simpa only [(factor_sums ht i j).1, (factor_sums ht i j).2] using hb
  intro i j
  by_cases hij : i ≤ j
  · exact hup i j hij
  · have hs : A j i = A i j := congrArg (fun M => M i j) hSymm
    have hr : (R.transpose*R) j i = (R.transpose*R) i j := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]; apply Finset.sum_congr rfl; intro k hk; ring
    have ha : (entrywiseAbs R.transpose*entrywiseAbs R) j i =
        (entrywiseAbs R.transpose*entrywiseAbs R) i j := by
      simp only [Matrix.mul_apply, entrywiseAbs, Matrix.transpose_apply]; apply Finset.sum_congr rfl; intro k hk; ring
    simpa only [factorPerturbation, Matrix.sub_apply, hr, ha, hs] using hup j i (le_of_not_ge hij)

lemma row_perturbation {n : ℕ} (t x : Fin n → ℝ) (g r : ℝ) (hg : 0 ≤ g)
    (hr : |r| ≤ g * ∑ j, |t j*x j|) :
    ∃ e : Fin n → ℝ, (∑ j, e j*x j) = r ∧ ∀ j, |e j| ≤ g*|t j| := by
  let s : ℝ := ∑ j, |t j*x j|
  have hs : 0 ≤ s := Finset.sum_nonneg (by intro j hj; exact abs_nonneg _)
  by_cases hz : s=0
  · have hr0 : r=0 := by change |r| ≤ g*s at hr; rw [hz, mul_zero] at hr; exact abs_eq_zero.mp (le_antisymm hr (abs_nonneg _))
    refine ⟨0, by simp [hr0], ?_⟩
    intro j; simpa using mul_nonneg hg (abs_nonneg (t j))
  · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    let w : Fin n → ℝ := fun j => if 0 ≤ x j then |t j| else -|t j|
    have hw (j : Fin n) : |w j| = |t j| := by dsimp [w]; split_ifs <;> simp
    have hwx (j : Fin n) : w j*x j = |t j*x j| := by
      dsimp [w]; rw [abs_mul]; split_ifs with hj
      · rw [abs_of_nonneg hj]
      · rw [abs_of_neg (lt_of_not_ge hj)]; ring
    have hscale : |r/s| ≤ g := by
      rw [abs_div, abs_of_pos hsp]
      exact (div_le_iff₀ hsp).2 hr
    refine ⟨fun j => (r/s)*w j, ?_, ?_⟩
    · simp only [mul_assoc, hwx, ← Finset.mul_sum]
      change r/s*s=r
      exact div_mul_cancel₀ r hz
    · intro j
      rw [abs_mul, hw]
      exact mul_le_mul_of_nonneg_right hscale (abs_nonneg _)

lemma solve_error {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ} {b x : Fin n → ℝ}
    {g : ℝ} (hg : 0 ≤ g)
    (herr : ∀ i, |T.mulVec x i - b i| ≤ g * ∑ k, |T i k*x k|) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ,
      (T+E).mulVec x = b ∧ ∀ i j, |E i j| ≤ g*|T i j| := by
  have hrow (i : Fin n) := row_perturbation (T i) x g (b i-T.mulVec x i) hg
    (by simpa [abs_sub_comm] using herr i)
  choose E he hb using hrow
  refine ⟨E, ?_, hb⟩
  funext i
  change (∑ j, (T i j+E i j)*x j) = b i
  simp only [add_mul, Finset.sum_add_distrib, he]
  change T.mulVec x i + (b i-T.mulVec x i) = b i
  ring

lemma product_bound {n : ℕ} (X Y S T : Matrix (Fin n) (Fin n) ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : ∀ i j, |X i j| ≤ a*|S i j|) (hy : ∀ i j, |Y i j| ≤ b*|T i j|)
    (i j : Fin n) :
    |(X*Y) i j| ≤ (a*b)*(entrywiseAbs S*entrywiseAbs T) i j := by
  calc
    _ ≤ ∑ k, |X i k*Y k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (a*|S i k|)*(b*|T k j|) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul (hx i k) (hy k j) (abs_nonneg _) (mul_nonneg ha (abs_nonneg _))
    _ = _ := by
      simp only [Matrix.mul_apply, entrywiseAbs, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k hk; ring

/-- The complete Cholesky Solve theorem, including both componentwise bounds.
The square-root model and absence of exceptional arithmetic are explicit in
`execution`; no algorithmic backward-error estimate is assumed. There is no
symmetry requirement on the final perturbation. The statement includes n=0
and u=0. -/
theorem cholesky_solve
    {n : ℕ} (u : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (R : Matrix (Fin n) (Fin n) ℝ) (y x : Fin n → ℝ)
    (hu : 0 ≤ u) (hsmall : ((n + 1 : ℕ) : ℝ) * u < 1)
    (hA : A.PosDef) (hSymm : A.transpose = A)
    (execution : SolveTrace u A b R y x) :
    ∃ ΔA : Matrix (Fin n) (Fin n) ℝ,
      (A + ΔA).mulVec x = b ∧
      (∀ i j, |ΔA i j| ≤
        (gamma u (n + 1) + 2 * gamma u n + (gamma u n) ^ 2) *
          (entrywiseAbs R.transpose * entrywiseAbs R) i j) ∧
      (∀ i j,
        (gamma u (n + 1) + 2 * gamma u n + (gamma u n) ^ 2) *
            (entrywiseAbs R.transpose * entrywiseAbs R) i j ≤
        (3 * gamma u (n + 1) + (gamma u n) ^ 2) *
          (entrywiseAbs R.transpose * entrywiseAbs R) i j) := by
  have hn : (n:ℝ)*u < 1 := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hu) hsmall
  have hg := gamma_nonneg hu hn
  obtain ⟨EL, hEL, hbEL⟩ := solve_error hg (forward_row hu hn execution.forward)
  obtain ⟨EU, hEU, hbEU⟩ := solve_error hg (backward_row hu hn execution.backward)
  have hf := factor_bound hu hsmall hSymm execution.factor
  have hid : A + solvePerturbation A R EL EU = (R.transpose+EL)*(R+EU) := by
    unfold solvePerturbation factorPerturbation
    noncomm_ring
  refine ⟨solvePerturbation A R EL EU, ?_, ?_, ?_⟩
  · rw [hid, ← Matrix.mulVec_mulVec, hEU, hEL]
  · intro i j
    have h1 := product_bound R.transpose EU R.transpose R (by norm_num : (0:ℝ) ≤ 1) hg
      (by intro i j; simp) hbEU i j
    have h2 := product_bound EL R R.transpose R hg (by norm_num : (0:ℝ) ≤ 1)
      hbEL (by intro i j; simp) i j
    have h3 := product_bound EL EU R.transpose R hg hg hbEL hbEU i j
    have hs : |solvePerturbation A R EL EU i j| ≤
        |factorPerturbation A R i j| + |(R.transpose*EU) i j| +
          |(EL*R) i j| + |(EL*EU) i j| := by
      unfold solvePerturbation
      change |((factorPerturbation A R i j + (R.transpose*EU) i j) + (EL*R) i j) + (EL*EU) i j| ≤ _
      exact (abs_add_le _ _).trans (add_le_add (abs_add_three _ _ _) le_rfl)
    have hall := add_le_add (add_le_add (add_le_add (hf i j) h1) h2) h3
    exact hs.trans (by convert hall using 1 <;> ring)
  · intro i j
    have hm := gamma_mono hu (Nat.le_succ n) hsmall
    have hpos : 0 ≤ (entrywiseAbs R.transpose*entrywiseAbs R) i j := by
      simp only [Matrix.mul_apply, entrywiseAbs]
      apply Finset.sum_nonneg
      intro k hk
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    exact mul_le_mul_of_nonneg_right (by nlinarith) hpos

end

end Research.CholeskySolve
