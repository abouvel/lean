import Mathlib

/-!
Statement skeleton for source.txt, theorem:cholesky_solve.
All arithmetic takes place in ℝ, with local relative-error certificates for
precisely the primitive operations executed. These certificates express the
standard no-overflow/no-underflow abstraction. The diagonal certificate also
explicitly specifies rounding of sqrt, which is used by the paper but omitted
from its displayed four-operation model. No backward-error bound is a run premise.
-/
namespace CholeskySolve

noncomputable section

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- Problem-size dependent deterministic rounding constant. -/
def gamma (u : ℝ) (m : ℕ) : ℝ := (m : ℝ) * u / (1 - (m : ℝ) * u)

/-- Entrywise absolute value, not a matrix norm. -/
def absMatrix {n : ℕ} (M : Mat n) : Mat n := fun i j => |M i j|

/-- A local standard-model rounding step. For sqrt the exact input here is
`Real.sqrt s`; this is an explicit primitive sqrt-rounding specification. -/
def RoundOK (u : ℝ) (rnd : ℝ → ℝ) (t : ℝ) : Prop :=
  ∃ δ : ℝ, |δ| ≤ u ∧ rnd t = t * (1 + δ)

/-- Sequential accumulation after the first rounded product. -/
def dotAux (rnd : ℝ → ℝ) : List (ℝ × ℝ) → ℝ → ℝ
  | [], s => s
  | (a, b) :: xs, s => dotAux rnd xs (rnd (s + rnd (a * b)))

def dot (rnd : ℝ → ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 0
  | (a, b) :: xs => dotAux rnd xs (rnd (a * b))

/-- Local certificates for every multiplication and addition in `dotAux`. -/
def dotAuxValid (u : ℝ) (rnd : ℝ → ℝ) : List (ℝ × ℝ) → ℝ → Prop
  | [], _ => True
  | (a, b) :: xs, s =>
      RoundOK u rnd (a * b) ∧ RoundOK u rnd (s + rnd (a * b)) ∧
      dotAuxValid u rnd xs (rnd (s + rnd (a * b)))

def dotValid (u : ℝ) (rnd : ℝ → ℝ) : List (ℝ × ℝ) → Prop
  | [] => True
  | (a, b) :: xs => RoundOK u rnd (a * b) ∧ dotAuxValid u rnd xs (rnd (a * b))

/-- Empty dot products incur no artificial subtraction or addition rounding. -/
def subDot (rnd : ℝ → ℝ) (c : ℝ) (xs : List (ℝ × ℝ)) : ℝ :=
  match xs with
  | [] => c
  | _ :: _ => rnd (c - dot rnd xs)

def subDotValid (u : ℝ) (rnd : ℝ → ℝ) (c : ℝ)
    (xs : List (ℝ × ℝ)) : Prop :=
  dotValid u rnd xs ∧ match xs with
    | [] => True
    | _ :: _ => RoundOK u rnd (c - dot rnd xs)

/-- Sequential dot product, subtraction, and final rounded division. -/
def update (rnd : ℝ → ℝ) (c d : ℝ) (xs : List (ℝ × ℝ)) : ℝ :=
  rnd (subDot rnd c xs / d)

def updateValid (u : ℝ) (rnd : ℝ → ℝ) (c d : ℝ)
    (xs : List (ℝ × ℝ)) : Prop :=
  d ≠ 0 ∧ subDotValid u rnd c xs ∧ RoundOK u rnd (subDot rnd c xs / d)

/-- Indices are accumulated in increasing order. -/
def choleskyTerms {n : ℕ} (R : Mat n) (i j : Fin n) : List (ℝ × ℝ) :=
  ((List.finRange n).filter (fun k => k < i)).map (fun k => (R k i, R k j))

def forwardTerms {n : ℕ} (T : Mat n) (z : Vec n) (i : Fin n) : List (ℝ × ℝ) :=
  ((List.finRange n).filter (fun k => k < i)).map (fun k => (T i k, z k))

def backwardTerms {n : ℕ} (T : Mat n) (z : Vec n) (i : Fin n) : List (ℝ × ℝ) :=
  ((List.finRange n).filter (fun k => i < k)).map (fun k => (T i k, z k))

/-- Successful columnwise upper Cholesky execution: off-diagonal updates for
 i < j followed by a positive-pivot rounded square root for entry (j,j).
 The triangular dependency order makes these equations an operational run
 relation; the only inequalities assumed here concern primitive rounding. -/
structure CholeskyRun {n : ℕ} (u : ℝ) (rnd : ℝ → ℝ) (A R : Mat n) : Prop where
  upper : ∀ i j, j < i → R i j = 0
  offdiag_valid : ∀ i j, i < j →
    updateValid u rnd (A i j) (R i i) (choleskyTerms R i j)
  offdiag_value : ∀ i j, i < j →
    R i j = update rnd (A i j) (R i i) (choleskyTerms R i j)
  diag_valid : ∀ j, subDotValid u rnd (A j j) (choleskyTerms R j j)
  pivot_positive : ∀ j, 0 < subDot rnd (A j j) (choleskyTerms R j j)
  sqrt_valid : ∀ j,
    RoundOK u rnd (Real.sqrt (subDot rnd (A j j) (choleskyTerms R j j)))
  diag_value : ∀ j,
    R j j = rnd (Real.sqrt (subDot rnd (A j j) (choleskyTerms R j j)))

/-- Forward substitution, in increasing row order. -/
structure ForwardRun {n : ℕ} (u : ℝ) (rnd : ℝ → ℝ)
    (T : Mat n) (b z : Vec n) : Prop where
  lower : ∀ i j, i < j → T i j = 0
  valid : ∀ i, updateValid u rnd (b i) (T i i) (forwardTerms T z i)
  value : ∀ i, z i = update rnd (b i) (T i i) (forwardTerms T z i)

/-- Backward substitution, in decreasing row order. The inner product within
 each row is accumulated in increasing column order. -/
structure BackwardRun {n : ℕ} (u : ℝ) (rnd : ℝ → ℝ)
    (T : Mat n) (b z : Vec n) : Prop where
  upper : ∀ i j, j < i → T i j = 0
  valid : ∀ i, updateValid u rnd (b i) (T i i) (backwardTerms T z i)
  value : ∀ i, z i = update rnd (b i) (T i i) (backwardTerms T z i)

/-- The three actual stages, with shared computed intermediate values. -/
structure SolveRun {n : ℕ} (u : ℝ) (rnd : ℝ → ℝ)
    (A : Mat n) (b : Vec n) (R : Mat n) (y x : Vec n) : Prop where
  factorization : CholeskyRun u rnd A R
  forward : ForwardRun u rnd R.transpose b y
  backward : BackwardRun u rnd R y x

/-- Symmetric factorization residual; symmetry follows from symmetry of A. -/
def factorResidual {n : ℕ} (A R : Mat n) : Mat n := R.transpose * R - A

/-- Total solve perturbation. L and U are the independently constructed
 forward and backward solve perturbations, respectively. -/
def solvePerturbation {n : ℕ} (A R L U : Mat n) : Mat n :=
  factorResidual A R + R.transpose * U + L * R + L * U

lemma gamma_nonneg {u : ℝ} (hu : 0 ≤ u) {m : ℕ} (hm : (m : ℝ) * u < 1) :
    0 ≤ gamma u m := by
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

lemma gamma_mono {u : ℝ} (hu : 0 ≤ u) {m k : ℕ} (hmk : m ≤ k)
    (hk : (k : ℝ) * u < 1) : gamma u m ≤ gamma u k := by
  have hmk' : (m : ℝ) * u ≤ (k : ℝ) * u :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hmk) hu
  unfold gamma
  apply (div_le_div_iff₀ (by linarith : 0 < 1 - (m : ℝ) * u)
    (by linarith : 0 < 1 - (k : ℝ) * u)).2
  nlinarith

lemma gamma_add {u : ℝ} (hu : 0 ≤ u) (a b : ℕ)
    (hab : ((a + b : ℕ) : ℝ) * u < 1) :
    gamma u a + gamma u b + gamma u a * gamma u b ≤ gamma u (a + b) := by
  have ha : 0 ≤ (a : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hb : 0 ≤ (b : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hab' : ((a : ℝ) + (b : ℝ)) * u < 1 := by simpa using hab
  have hda : 0 < 1 - (a : ℝ) * u := by nlinarith
  have hdb : 0 < 1 - (b : ℝ) * u := by nlinarith
  have hdab : 0 < 1 - ((a : ℝ) + (b : ℝ)) * u := by linarith
  have he : gamma u a + gamma u b + gamma u a * gamma u b =
      1 / ((1 - (a : ℝ) * u) * (1 - (b : ℝ) * u)) - 1 := by
    have aux (x y : ℝ) (hx : 1 - x ≠ 0) (hy : 1 - y ≠ 0) :
        x / (1 - x) + y / (1 - y) + (x / (1 - x)) * (y / (1 - y)) =
          1 / ((1 - x) * (1 - y)) - 1 := by
      field_simp
      ring
    exact aux _ _ (ne_of_gt hda) (ne_of_gt hdb)
  have hf : gamma u (a + b) = 1 / (1 - ((a : ℝ) + (b : ℝ)) * u) - 1 := by
    unfold gamma
    push_cast
    field_simp
    ring
  rw [he, hf]
  apply sub_le_sub_right
  apply one_div_le_one_div_of_le hdab
  nlinarith [mul_nonneg ha hb]

lemma round_error {u : ℝ} {rnd : ℝ → ℝ} {t : ℝ} (h : RoundOK u rnd t) :
    |rnd t - t| ≤ u * |t| := by
  obtain ⟨δ, hδ, he⟩ := h
  rw [he, show t * (1 + δ) - t = δ * t by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)

lemma inv_round_error {u δ : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) (hδ : |δ| ≤ u) :
    |(1 + δ)⁻¹ - 1| ≤ gamma u 1 := by
  have hδ' := abs_le.mp hδ
  have hq : 0 < 1 + δ := by linarith
  rw [show (1 + δ)⁻¹ - 1 = -δ / (1 + δ) by field_simp; ring]
  rw [abs_div, abs_neg, abs_of_pos hq]
  unfold gamma
  simp only [Nat.cast_one, one_mul]
  exact div_le_div₀ hu hδ (by linarith) (by linarith)

lemma coeff_mul {u p q : ℝ} (hu : 0 ≤ u) {a b : ℕ}
    (hab : ((a + b : ℕ) : ℝ) * u < 1)
    (hp : |p - 1| ≤ gamma u a) (hq : |q - 1| ≤ gamma u b) :
    |p * q - 1| ≤ gamma u (a + b) := by
  have ha : (a : ℝ) * u < 1 := by
    have : (a : ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right a b
    nlinarith
  have hb : (b : ℝ) * u < 1 := by
    have : (b : ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left b a
    nlinarith
  calc
    |p * q - 1| = |(p - 1) + (q - 1) + (p - 1) * (q - 1)| := by congr 1; ring
    _ ≤ |p - 1| + |q - 1| + |p - 1| * |q - 1| := by
      calc
        _ ≤ |(p - 1) + (q - 1)| + |(p - 1) * (q - 1)| := abs_add_le _ _
        _ ≤ _ := by rw [abs_mul]; gcongr; exact abs_add_le _ _
    _ ≤ gamma u a + gamma u b + gamma u a * gamma u b := by
      exact add_le_add (add_le_add hp hq)
        (mul_le_mul hp hq (abs_nonneg _) (gamma_nonneg hu ha))
    _ ≤ gamma u (a + b) := gamma_add hu a b hab


lemma u_le_gamma {u : ℝ} (hu : 0 ≤ u) {m : ℕ} (hm : 1 ≤ m)
    (hsmall : (m : ℝ) * u < 1) : u ≤ gamma u m := by
  have hu1 : u < 1 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have h : u ≤ gamma u 1 := by
    unfold gamma
    simp only [Nat.cast_one, one_mul]
    apply (le_div_iff₀ (by linarith : 0 < 1 - u)).2
    nlinarith
  exact h.trans (gamma_mono hu hm hsmall)

lemma round_extend {u : ℝ} {rnd : ℝ → ℝ} (hu : 0 ≤ u)
    {m : ℕ} (hsmall : ((m + 1 : ℕ) : ℝ) * u < 1)
    {s t B : ℝ} (hB : 0 ≤ B) (ht : |t| ≤ B)
    (hs : |s - t| ≤ gamma u m * B) (hr : RoundOK u rnd s) :
    |rnd s - t| ≤ gamma u (m + 1) * B := by
  have hm : (m : ℝ) * u < 1 := by
    have : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right m 1
    nlinarith
  have hu1 : u < 1 := by
    have : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
    nlinarith
  have hsabs : |s| ≤ (1 + gamma u m) * B := by
    calc
      |s| = |s - t + t| := by congr 1; ring
      _ ≤ |s - t| + |t| := abs_add_le _ _
      _ ≤ gamma u m * B + B := add_le_add hs ht
      _ = _ := by ring
  calc
    |rnd s - t| ≤ |rnd s - s| + |s - t| := abs_sub_le _ _ _
    _ ≤ u * ((1 + gamma u m) * B) + gamma u m * B :=
      add_le_add ((round_error hr).trans (mul_le_mul_of_nonneg_left hsabs hu)) hs
    _ = (gamma u m + u + gamma u m * u) * B := by ring
    _ ≤ (gamma u m + gamma u 1 + gamma u m * gamma u 1) * B := by
      have h := u_le_gamma hu (m := 1) (by omega) (by simpa using hu1)
      gcongr
      exact gamma_nonneg hu hm
    _ ≤ gamma u (m + 1) * B := mul_le_mul_of_nonneg_right (gamma_add hu m 1 hsmall) hB

private def products (xs : List (ℝ × ℝ)) : ℝ := (xs.map fun p => p.1 * p.2).sum
private def magnitudes (xs : List (ℝ × ℝ)) : ℝ := (xs.map fun p => |p.1 * p.2|).sum

private lemma magnitudes_nonneg (xs : List (ℝ × ℝ)) : 0 ≤ magnitudes xs := by
  unfold magnitudes
  exact List.sum_nonneg (by
    intro x hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _)

private lemma products_abs (xs : List (ℝ × ℝ)) : |products xs| ≤ magnitudes xs := by
  induction xs with
  | nil => simp [products, magnitudes]
  | cons p xs ih =>
    simpa only [products, magnitudes, List.map_cons, List.sum_cons] using (abs_add_le (p.1 * p.2) (products xs)).trans
      (add_le_add le_rfl ih)

private lemma dotAux_error {u : ℝ} {rnd : ℝ → ℝ} (hu : 0 ≤ u)
    (xs : List (ℝ × ℝ)) {m : ℕ} (hm : 1 ≤ m)
    (hsmall : ((m + xs.length : ℕ) : ℝ) * u < 1)
    {s t B : ℝ} (hB : 0 ≤ B) (ht : |t| ≤ B)
    (hs : |s - t| ≤ gamma u m * B)
    (hv : dotAuxValid u rnd xs s) :
    |dotAux rnd xs s - (t + products xs)| ≤
      gamma u (m + xs.length) * (B + magnitudes xs) := by
  induction xs generalizing m s t B with
  | nil => simpa [dotAux, products, magnitudes] using hs
  | cons p xs ih =>
    obtain ⟨hvprod, hvadd, hvrest⟩ := hv
    have hm1 : ((m + 1 : ℕ) : ℝ) * u < 1 := by
      have : ((m + 1 : ℕ) : ℝ) ≤ ((m + (p :: xs).length : ℕ) : ℝ) := by
        exact_mod_cast (by simp : m + 1 ≤ m + (p :: xs).length)
      nlinarith
    have hm0 : (m : ℝ) * u < 1 := by
      have : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right m 1
      nlinarith
    have heprod : |rnd (p.1 * p.2) - p.1 * p.2| ≤ gamma u m * |p.1 * p.2| :=
      (round_error hvprod).trans (mul_le_mul_of_nonneg_right (u_le_gamma hu hm hm0) (abs_nonneg _))
    have headd : |(s + rnd (p.1 * p.2)) - (t + p.1 * p.2)| ≤
        gamma u m * (B + |p.1 * p.2|) := by
      calc
        _ = |(s - t) + (rnd (p.1 * p.2) - p.1 * p.2)| := by congr 1; ring
        _ ≤ |s - t| + |rnd (p.1 * p.2) - p.1 * p.2| := abs_add_le _ _
        _ ≤ gamma u m * B + gamma u m * |p.1 * p.2| := add_le_add hs heprod
        _ = _ := by ring
    have he := round_extend hu hm1 (by positivity : 0 ≤ B + |p.1 * p.2|)
      ((abs_add_le t (p.1 * p.2)).trans (add_le_add ht le_rfl)) headd hvadd
    have hh := ih (m := m + 1) (by omega) (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsmall)
      (by positivity : 0 ≤ B + |p.1 * p.2|)
      ((abs_add_le t (p.1 * p.2)).trans (add_le_add ht le_rfl)) he hvrest
    simpa [dotAux, products, magnitudes, List.length_cons, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm, add_assoc] using hh

/-- Forward error for sequential accumulation, counting the first product once. -/
private lemma dot_error {u : ℝ} {rnd : ℝ → ℝ} (hu : 0 ≤ u)
    (xs : List (ℝ × ℝ)) (hsmall : (xs.length : ℝ) * u < 1)
    (hv : dotValid u rnd xs) :
    |dot rnd xs - products xs| ≤ gamma u xs.length * magnitudes xs := by
  cases xs with
  | nil => simp [dot, products, magnitudes]
  | cons p xs =>
    obtain ⟨hp, hxs⟩ := hv
    have hu1 : u < 1 := by
      have : (1 : ℝ) ≤ ((p :: xs).length : ℝ) := by simp
      nlinarith
    have he : |rnd (p.1 * p.2) - p.1 * p.2| ≤ gamma u 1 * |p.1 * p.2| :=
      (round_error hp).trans (mul_le_mul_of_nonneg_right
        (u_le_gamma hu (m := 1) (by omega) (by simpa using hu1)) (abs_nonneg _))
    have hh := dotAux_error hu xs (m := 1) (by omega)
      (by simpa [Nat.add_comm] using hsmall) (abs_nonneg (p.1 * p.2)) le_rfl he hxs
    simpa [dot, products, magnitudes, Nat.add_comm] using hh


lemma small_of_le {u : ℝ} (hu : 0 ≤ u) {m k : ℕ} (hmk : m ≤ k)
    (hk : (k : ℝ) * u < 1) : (m : ℝ) * u < 1 :=
  (mul_le_mul_of_nonneg_right (by exact_mod_cast hmk) hu).trans_lt hk

private lemma residual_bound {u c v d : ℝ} {rnd : ℝ → ℝ}
    (hu : 0 ≤ u) (xs : List (ℝ × ℝ)) {m : ℕ}
    (hsmall : (m : ℝ) * u < 1) (hlen : xs.length ≤ m)
    (hv : dotValid u rnd xs) (hd : |d - 1| ≤ gamma u m)
    (he : c = v * d + dot rnd xs) :
    |v + products xs - c| ≤ gamma u m * (|v| + magnitudes xs) := by
  have hdot := (dot_error hu xs (small_of_le hu hlen hsmall) hv).trans
    (mul_le_mul_of_nonneg_right (gamma_mono hu hlen hsmall) (magnitudes_nonneg xs))
  calc
    |v + products xs - c| = |v * (1 - d) + (products xs - dot rnd xs)| := by rw [he]; congr 1; ring
    _ ≤ |v| * |1 - d| + |products xs - dot rnd xs| := by
      simpa only [abs_mul] using abs_add_le (v * (1 - d)) (products xs - dot rnd xs)
    _ ≤ |v| * gamma u m + gamma u m * magnitudes xs := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (by simpa only [abs_sub_comm] using hd) (abs_nonneg _)
      · simpa only [abs_sub_comm] using hdot
    _ = _ := by ring

/-- The empty row uses one reciprocal factor; other rows use two. -/
private lemma update_residual {u c d : ℝ} {rnd : ℝ → ℝ}
    (hu : 0 ≤ u) (xs : List (ℝ × ℝ)) {m : ℕ}
    (hm : 1 ≤ m) (hmore : xs ≠ [] → 2 ≤ m)
    (hlen : xs.length ≤ m) (hsmall : (m : ℝ) * u < 1)
    (hv : updateValid u rnd c d xs) :
    |d * update rnd c d xs + products xs - c| ≤
      gamma u m * (|d * update rnd c d xs| + magnitudes xs) := by
  obtain ⟨hd, hsub, δ, hδ, hdiv⟩ := hv
  have hu1 : u < 1 := by simpa using small_of_le hu hm hsmall
  have hq : 1 + δ ≠ 0 := by have := (abs_le.mp hδ).1; linarith
  have hrec : subDot rnd c xs = d * update rnd c d xs * (1 + δ)⁻¹ := by
    unfold update
    rw [hdiv]
    field_simp
  cases xs with
  | nil =>
    have he : c = d * update rnd c d [] * (1 + δ)⁻¹ + dot rnd [] := by
      simpa [subDot, dot] using hrec
    exact residual_bound hu [] hsmall hlen hsub.1
      ((inv_round_error hu hu1 hδ).trans (gamma_mono hu hm hsmall)) he
  | cons p xs =>
    obtain ⟨hvdot, ε, hε, hsubeq⟩ := hsub
    have hp : 2 ≤ m := hmore (by simp)
    have hqε : 1 + ε ≠ 0 := by have := (abs_le.mp hε).1; linarith
    have he : c = d * update rnd c d (p :: xs) * ((1 + δ)⁻¹ * (1 + ε)⁻¹) + dot rnd (p :: xs) := by
      have hs : subDot rnd c (p :: xs) = (c - dot rnd (p :: xs)) * (1 + ε) := hsubeq
      rw [hs] at hrec
      apply (mul_right_cancel₀ hqε)
      calc
        c * (1 + ε) = (c - dot rnd (p :: xs)) * (1 + ε) + dot rnd (p :: xs) * (1 + ε) := by ring
        _ = d * update rnd c d (p :: xs) * (1 + δ)⁻¹ + dot rnd (p :: xs) * (1 + ε) := by rw [hrec]
        _ = _ := by field_simp
    apply residual_bound hu (p :: xs) hsmall hlen hvdot _ he
    exact (coeff_mul hu (small_of_le hu hp hsmall)
      (inv_round_error hu hu1 hδ) (inv_round_error hu hu1 hε)).trans (gamma_mono hu hp hsmall)

/-- Squaring the rounded square root introduces two reciprocal factors. -/
private lemma sqrt_residual {u c z : ℝ} {rnd : ℝ → ℝ}
    (hu : 0 ≤ u) (xs : List (ℝ × ℝ)) {m : ℕ}
    (hm : 2 ≤ m) (hmore : xs ≠ [] → 3 ≤ m)
    (hlen : xs.length ≤ m) (hsmall : (m : ℝ) * u < 1)
    (hv : subDotValid u rnd c xs) (hpos : 0 < subDot rnd c xs)
    (hsqrt : RoundOK u rnd (Real.sqrt (subDot rnd c xs)))
    (hz : z = rnd (Real.sqrt (subDot rnd c xs))) :
    |z ^ 2 + products xs - c| ≤ gamma u m * (|z ^ 2| + magnitudes xs) := by
  obtain ⟨δ, hδ, hround⟩ := hsqrt
  have hu1 : u < 1 := by simpa using small_of_le hu (show 1 ≤ m by omega) hsmall
  have hq : 1 + δ ≠ 0 := by have := (abs_le.mp hδ).1; linarith
  have hinv := inv_round_error hu hu1 hδ
  have hinv2 : |(1 + δ)⁻¹ * (1 + δ)⁻¹ - 1| ≤ gamma u 2 :=
    coeff_mul hu (small_of_le hu hm hsmall) hinv hinv
  have hrec : subDot rnd c xs = z ^ 2 * ((1 + δ)⁻¹ * (1 + δ)⁻¹) := by
    rw [hz, hround, mul_pow, Real.sq_sqrt (le_of_lt hpos)]
    field_simp
  cases xs with
  | nil =>
    apply residual_bound hu [] hsmall hlen hv.1
      (hinv2.trans (gamma_mono hu hm hsmall))
    simpa [subDot, dot] using hrec
  | cons p xs =>
    obtain ⟨hvdot, ε, hε, hsubeq⟩ := hv
    have hp : 3 ≤ m := hmore (by simp)
    have hqε : 1 + ε ≠ 0 := by have := (abs_le.mp hε).1; linarith
    have he : c = z ^ 2 * (((1 + δ)⁻¹ * (1 + δ)⁻¹) * (1 + ε)⁻¹) + dot rnd (p :: xs) := by
      have hs : subDot rnd c (p :: xs) = (c - dot rnd (p :: xs)) * (1 + ε) := hsubeq
      rw [hs] at hrec
      apply (mul_right_cancel₀ hqε)
      calc
        c * (1 + ε) = (c - dot rnd (p :: xs)) * (1 + ε) + dot rnd (p :: xs) * (1 + ε) := by ring
        _ = z ^ 2 * ((1 + δ)⁻¹ * (1 + δ)⁻¹) + dot rnd (p :: xs) * (1 + ε) := by rw [hrec]
        _ = _ := by field_simp
    apply residual_bound hu (p :: xs) hsmall hlen hvdot _ he
    exact (coeff_mul hu (small_of_le hu hp hsmall) hinv2
      (inv_round_error hu hu1 hε)).trans (gamma_mono hu hp hsmall)


private lemma filtered_sum {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (f : Fin n → ℝ) :
    (((List.finRange n).filter fun k => p k).map f).sum =
      ∑ k, if p k then f k else 0 := by
  rw [← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
  simp [List.toFinset_filter, Finset.sum_filter]

private lemma filtered_length_lt {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (i : Fin n) (hi : ¬p i) :
    ((List.finRange n).filter fun k => p k).length < n := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  have he : ((List.finRange n).filter fun k => p k).toFinset =
      Finset.univ.filter p := by ext k; simp
  rw [he]
  suffices h : (Finset.univ.filter p).card < (Finset.univ : Finset (Fin n)).card by
    simpa using h
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  have : i ∈ Finset.univ.filter p := by rw [heq]; simp
  simp [hi] at this

private lemma split_sum {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (i : Fin n) (hi : ¬p i) (f : Fin n → ℝ)
    (hsupport : ∀ k, k ≠ i → ¬p k → f k = 0) :
    ∑ k, f k = f i + ∑ k, if p k then f k else 0 := by
  calc
    ∑ k, f k = ∑ k, ((if k = i then f k else 0) + (if p k then f k else 0)) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hki : k = i
      · subst k; simp [hi]
      · by_cases hp : p k
        · simp [hki, hp]
        · simp [hki, hp, hsupport k hki hp]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

private lemma forward_residual {n : ℕ} {u : ℝ} {rnd : ℝ → ℝ}
    {T : Mat n} {b z : Vec n} (hu : 0 ≤ u) (hsmall : (n : ℝ) * u < 1)
    (hrun : ForwardRun u rnd T b z) (i : Fin n) :
    |T.mulVec z i - b i| ≤ gamma u n * (∑ k, |T i k * z k|) := by
  have hlen : (forwardTerms T z i).length < n := by
    simpa [forwardTerms] using filtered_length_lt (fun k => k < i) i (lt_irrefl i)
  have hmore : forwardTerms T z i ≠ [] → 2 ≤ n := by
    intro h
    have : 0 < (forwardTerms T z i).length := List.length_pos_iff.mpr h
    omega
  have he := update_residual hu (forwardTerms T z i) (show 1 ≤ n by omega)
    hmore (by omega) hsmall (hrun.valid i)
  rw [← hrun.value i] at he
  have hsum : T.mulVec z i = T i i * z i + products (forwardTerms T z i) := by
    unfold Matrix.mulVec dotProduct
    rw [split_sum (fun k => k < i) i (lt_irrefl i)]
    · simp only [products, forwardTerms, List.map_map, Function.comp_def]
      rw [filtered_sum]
    · intro k hki hp
      change T i k * z k = 0
      rw [hrun.lower i k (by exact lt_of_le_of_ne (le_of_not_gt hp) (Ne.symm hki)), zero_mul]
  have habs : (∑ k, |T i k * z k|) = |T i i * z i| + magnitudes (forwardTerms T z i) := by
    rw [split_sum (fun k => k < i) i (lt_irrefl i)]
    · simp only [magnitudes, forwardTerms, List.map_map, Function.comp_def]
      rw [filtered_sum]
    · intro k hki hp
      rw [hrun.lower i k (lt_of_le_of_ne (le_of_not_gt hp) (Ne.symm hki)), zero_mul, abs_zero]
  simpa only [hsum, habs] using he

private lemma backward_residual {n : ℕ} {u : ℝ} {rnd : ℝ → ℝ}
    {T : Mat n} {b z : Vec n} (hu : 0 ≤ u) (hsmall : (n : ℝ) * u < 1)
    (hrun : BackwardRun u rnd T b z) (i : Fin n) :
    |T.mulVec z i - b i| ≤ gamma u n * (∑ k, |T i k * z k|) := by
  have hlen : (backwardTerms T z i).length < n := by
    simpa [backwardTerms] using filtered_length_lt (fun k => i < k) i (lt_irrefl i)
  have hmore : backwardTerms T z i ≠ [] → 2 ≤ n := by
    intro h
    have : 0 < (backwardTerms T z i).length := List.length_pos_iff.mpr h
    omega
  have he := update_residual hu (backwardTerms T z i) (show 1 ≤ n by omega)
    hmore (by omega) hsmall (hrun.valid i)
  rw [← hrun.value i] at he
  have hsum : T.mulVec z i = T i i * z i + products (backwardTerms T z i) := by
    unfold Matrix.mulVec dotProduct
    rw [split_sum (fun k => i < k) i (lt_irrefl i)]
    · simp only [products, backwardTerms, List.map_map, Function.comp_def]
      rw [filtered_sum]
    · intro k hki hp
      change T i k * z k = 0
      rw [hrun.upper i k (lt_of_le_of_ne (le_of_not_gt hp) hki), zero_mul]
  have habs : (∑ k, |T i k * z k|) = |T i i * z i| + magnitudes (backwardTerms T z i) := by
    rw [split_sum (fun k => i < k) i (lt_irrefl i)]
    · simp only [magnitudes, backwardTerms, List.map_map, Function.comp_def]
      rw [filtered_sum]
    · intro k hki hp
      rw [hrun.upper i k (lt_of_le_of_ne (le_of_not_gt hp) hki), zero_mul, abs_zero]
  simpa only [hsum, habs] using he

private lemma factor_residual_bound {n : ℕ} {u : ℝ} {rnd : ℝ → ℝ}
    {A R : Mat n} (hu : 0 ≤ u) (hsmall : ((n : ℝ) + 1) * u < 1)
    (hsymm : A.transpose = A) (hrun : CholeskyRun u rnd A R) :
    ∀ i j, |factorResidual A R i j| ≤
      gamma u (n + 1) * (absMatrix R.transpose * absMatrix R) i j := by
  have hsmall' : ((n + 1 : ℕ) : ℝ) * u < 1 := by simpa using hsmall
  suffices hhalf : ∀ i j, i ≤ j → |factorResidual A R i j| ≤
      gamma u (n + 1) * (absMatrix R.transpose * absMatrix R) i j by
    intro i j
    by_cases hij : i ≤ j
    · exact hhalf i j hij
    · have he := hhalf j i (le_of_lt (lt_of_not_ge hij))
      have ha : A j i = A i j := by
        have := congrArg (fun M : Mat n => M i j) hsymm
        exact this
      simpa only [factorResidual, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
        absMatrix, ha, mul_comm] using he
  intro i j hij
  have hlen : (choleskyTerms R i j).length < n := by
    simpa [choleskyTerms] using filtered_length_lt (fun k => k < i) i (lt_irrefl i)
  have hsum : (R.transpose * R) i j = R i i * R i j + products (choleskyTerms R i j) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
    rw [split_sum (fun k => k < i) i (lt_irrefl i)]
    · simp only [products, choleskyTerms, List.map_map, Function.comp_def]
      rw [filtered_sum]
    · intro k hki hp
      rw [hrun.upper k i (lt_of_le_of_ne (le_of_not_gt hp) (Ne.symm hki)), zero_mul]
  have habs : (absMatrix R.transpose * absMatrix R) i j =
      |R i i * R i j| + magnitudes (choleskyTerms R i j) := by
    simp only [Matrix.mul_apply, absMatrix, Matrix.transpose_apply, ← abs_mul]
    rw [split_sum (fun k => k < i) i (lt_irrefl i)]
    · simp only [magnitudes, choleskyTerms, List.map_map, Function.comp_def]
      rw [filtered_sum]
    · intro k hki hp
      rw [hrun.upper k i (lt_of_le_of_ne (le_of_not_gt hp) (Ne.symm hki)), zero_mul, abs_zero]
  by_cases heq : i = j
  · subst j
    have hm : 2 ≤ n + 1 := by omega
    have hmore : choleskyTerms R i i ≠ [] → 3 ≤ n + 1 := by
      intro h
      have : 0 < (choleskyTerms R i i).length := List.length_pos_iff.mpr h
      omega
    have he := sqrt_residual hu (choleskyTerms R i i) hm hmore (by omega) hsmall'
      (hrun.diag_valid i) (hrun.pivot_positive i) (hrun.sqrt_valid i) (hrun.diag_value i)
    simpa only [factorResidual, Matrix.sub_apply, hsum, habs, pow_two] using he
  · have hlt : i < j := lt_of_le_of_ne hij heq
    have he := update_residual hu (choleskyTerms R i j) (show 1 ≤ n + 1 by omega)
      (by intro; omega) (by omega) hsmall' (hrun.offdiag_valid i j hlt)
    rw [← hrun.offdiag_value i j hlt] at he
    simpa only [factorResidual, Matrix.sub_apply, hsum, habs] using he


/-- Distribute each scalar residual over the absolute row contributions. -/
private lemma row_perturbation {n : ℕ} (T : Mat n) (b z : Vec n)
    {g : ℝ} (hg : 0 ≤ g)
    (hres : ∀ i, |T.mulVec z i - b i| ≤ g * (∑ k, |T i k * z k|)) :
    ∃ E : Mat n, (T + E).mulVec z = b ∧ ∀ i k, |E i k| ≤ g * |T i k| := by
  let S : Fin n → ℝ := fun i => ∑ k, |T i k * z k|
  let r : Fin n → ℝ := fun i => T.mulVec z i - b i
  have hS : ∀ i, 0 ≤ S i := fun i => Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hr0 : ∀ i, S i = 0 → r i = 0 := by
    intro i hi
    apply abs_eq_zero.mp
    apply le_antisymm _ (abs_nonneg _)
    have hh : |r i| ≤ g * S i := hres i
    simpa only [hi, mul_zero] using hh
  have hratio : ∀ i, |r i / S i| ≤ g := by
    intro i
    by_cases hi : S i = 0
    · simp [hi, hg]
    · rw [abs_div, abs_of_nonneg (hS i)]
      exact (div_le_iff₀ (lt_of_le_of_ne (hS i) (Ne.symm hi))).2 (hres i)
  let sg : Fin n → ℝ := fun k => if 0 ≤ z k then 1 else -1
  have hsg : ∀ k, sg k * z k = |z k| := by
    intro k
    dsimp [sg]
    split_ifs with hk
    · simp [abs_of_nonneg hk]
    · simp [abs_of_neg (lt_of_not_ge hk)]
  have habssg : ∀ k, |sg k| = 1 := by intro k; dsimp [sg]; split_ifs <;> norm_num
  let E : Mat n := fun i k => -(r i / S i) * |T i k| * sg k
  refine ⟨E, ?_, ?_⟩
  · ext i
    rw [Matrix.add_mulVec, Pi.add_apply]
    have he : E.mulVec z i = -r i := by
      change (∑ k, E i k * z k) = -r i
      calc
        (∑ k, E i k * z k) = ∑ k, -(r i / S i) * |T i k * z k| := by
          apply Finset.sum_congr rfl
          intro k _
          dsimp [E]
          rw [mul_assoc, mul_assoc, hsg, abs_mul]
        _ = -(r i / S i) * S i := by rw [← Finset.mul_sum]
        _ = -r i := by
          by_cases hi : S i = 0
          · simp [hi, hr0 i hi]
          · field_simp
    rw [he]
    dsimp [r]
    ring
  · intro i k
    change |-(r i / S i) * |T i k| * sg k| ≤ _
    rw [abs_mul, abs_mul, abs_neg, abs_abs, habssg, mul_one]
    exact mul_le_mul_of_nonneg_right (hratio i) (abs_nonneg _)

private lemma matrix_product_bound {n : ℕ} (M N P Q : Mat n) {a b : ℝ}
    (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hM : ∀ i k, |M i k| ≤ a * |P i k|)
    (hN : ∀ k j, |N k j| ≤ b * |Q k j|) (i j : Fin n) :
    |(M * N) i j| ≤ (a * b) * (absMatrix P * absMatrix Q) i j := by
  rw [Matrix.mul_apply]
  calc
    |∑ k, M i k * N k j| ≤ ∑ k, |M i k * N k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (a * |P i k|) * (b * |Q k j|) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hM i k) (hN k j) (abs_nonneg _) (mul_nonneg ha (abs_nonneg _))
    _ = (a * b) * (absMatrix P * absMatrix Q) i j := by
      simp only [Matrix.mul_apply, absMatrix, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring


/-- Full selected Cholesky Solve theorem. The run certificates include absence
 of overflow/underflow at every used primitive and standard sqrt rounding.
 Both bounds are componentwise; no symmetry of ΔA is asserted. Dimension zero
 and exact arithmetic u=0 are included. No paper backward-error lemma is assumed. -/
theorem cholesky_solve
    {n : ℕ} (u : ℝ) (rnd : ℝ → ℝ) (A : Mat n) (b : Vec n)
    (R : Mat n) (y x : Vec n)
    (hu : 0 ≤ u) (hsmall : ((n : ℝ) + 1) * u < 1)
    (hsymm : A.transpose = A) (hpos : A.PosDef)
    (hrun : SolveRun u rnd A b R y x) :
    ∃ ΔA : Mat n,
      (A + ΔA).mulVec x = b ∧
      (∀ i j, |ΔA i j| ≤
        (gamma u (n + 1) + 2 * gamma u n + (gamma u n) ^ 2) *
          (absMatrix R.transpose * absMatrix R) i j) ∧
      (∀ i j,
        (gamma u (n + 1) + 2 * gamma u n + (gamma u n) ^ 2) *
            (absMatrix R.transpose * absMatrix R) i j ≤
        (3 * gamma u (n + 1) + (gamma u n) ^ 2) *
          (absMatrix R.transpose * absMatrix R) i j) := by
  have hsmall' : ((n + 1 : ℕ) : ℝ) * u < 1 := by simpa using hsmall
  have hn : (n : ℝ) * u < 1 := small_of_le hu (by omega) hsmall'
  have hgn : 0 ≤ gamma u n := gamma_nonneg hu hn
  obtain ⟨L, hLsolve, hL⟩ := row_perturbation R.transpose b y hgn
    (forward_residual hu hn hrun.forward)
  obtain ⟨U, hUsolve, hU⟩ := row_perturbation R y x hgn
    (backward_residual hu hn hrun.backward)
  have hf := factor_residual_bound hu hsmall hsymm hrun.factorization
  have hR (i j : Fin n) : |R i j| ≤ 1 * |R i j| := by simp
  have hRt (i j : Fin n) : |R.transpose i j| ≤ 1 * |R.transpose i j| := by simp
  have hRU (i j : Fin n) : |(R.transpose * U) i j| ≤
      gamma u n * (absMatrix R.transpose * absMatrix R) i j := by
    simpa using matrix_product_bound R.transpose U R.transpose R (by norm_num) hgn hRt hU i j
  have hLR (i j : Fin n) : |(L * R) i j| ≤
      gamma u n * (absMatrix R.transpose * absMatrix R) i j := by
    simpa using matrix_product_bound L R R.transpose R hgn (by norm_num) hL hR i j
  have hLU (i j : Fin n) : |(L * U) i j| ≤
      (gamma u n) ^ 2 * (absMatrix R.transpose * absMatrix R) i j := by
    simpa only [pow_two] using matrix_product_bound L U R.transpose R hgn hgn hL hU i j
  have hS (i j : Fin n) : 0 ≤ (absMatrix R.transpose * absMatrix R) i j := by
    simp only [Matrix.mul_apply, absMatrix]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  refine ⟨solvePerturbation A R L U, ?_, ?_, ?_⟩
  · have he : A + solvePerturbation A R L U = (R.transpose + L) * (R + U) := by
      unfold solvePerturbation factorResidual
      noncomm_ring
    rw [he, ← Matrix.mulVec_mulVec, hUsolve, hLsolve]
  · intro i j
    change |((factorResidual A R + R.transpose * U) + L * R + L * U) i j| ≤ _
    simp only [Matrix.add_apply]
    calc
      _ ≤ |factorResidual A R i j| + |(R.transpose * U) i j| + |(L * R) i j| + |(L * U) i j| := by
        exact (abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ gamma u (n + 1) * (absMatrix R.transpose * absMatrix R) i j +
          gamma u n * (absMatrix R.transpose * absMatrix R) i j +
          gamma u n * (absMatrix R.transpose * absMatrix R) i j +
          gamma u n ^ 2 * (absMatrix R.transpose * absMatrix R) i j :=
        add_le_add (add_le_add (add_le_add (hf i j) (hRU i j)) (hLR i j)) (hLU i j)
      _ = _ := by ring
  · intro i j
    apply mul_le_mul_of_nonneg_right _ (hS i j)
    have := gamma_mono hu (show n ≤ n + 1 by omega) hsmall'
    linarith

end

end CholeskySolve
