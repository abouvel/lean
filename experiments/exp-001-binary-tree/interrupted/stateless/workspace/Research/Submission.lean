import Mathlib

/-! A formalization of Algorithm 1 and Theorem 3.1 from Sahil Bhola's
"Self-contained Proof for Parallel Binary Tree Reduction". -/

namespace ParallelBinaryTree

open scoped BigOperators

def gamma (k : ℕ) (u : ℝ) : ℝ := (k : ℝ) * u / (1 - (k : ℝ) * u)

/-- Offset pairing: split at the ceiling half and pair corresponding nodes. -/
def pairAux {α : Type} : List (List α) → List (List α) → List (List α)
  | a :: as, b :: bs => (a ++ b) :: pairAux as bs
  | as, [] => as
  | [], bs => bs

def offsetPair {α : Type} (s : List (List α)) : List (List α) :=
  let q := (s.length + 1) / 2
  pairAux (s.take q) (s.drop q)

/-- Error for one occurrence in one level. Paired nodes get their addition's
error; an unavailable partner takes the unchanged carry branch (error zero). -/
def errorAux {α : Type} [DecidableEq α] (δ : ℕ → ℝ) (k : ℕ) (i : α) :
    List (List α) → List (List α) → ℝ
  | a :: as, b :: bs =>
      if i ∈ a ∨ i ∈ b then δ k else errorAux δ (k + 1) i as bs
  | _, _ => 0

def offsetError {α : Type} [DecidableEq α]
    (δ : ℕ → ℝ) (s : List (List α)) (i : α) : ℝ :=
  let q := (s.length + 1) / 2
  errorAux δ 0 i (s.take q) (s.drop q)

structure TreeState (n : ℕ) where
  blocks : List (List (Fin n))
  coeff : Fin n → ℝ

def initial (n : ℕ) : TreeState n where
  blocks := List.ofFn fun i : Fin n => [i]
  coeff := fun _ => 1

def round {n : ℕ} (δ : ℕ → ℝ) (s : TreeState n) : TreeState n where
  blocks := offsetPair s.blocks
  coeff := fun i => s.coeff i * (1 + offsetError δ s.blocks i)

def run {n : ℕ} (δ : ℕ → ℕ → ℝ) : ℕ → ℕ → TreeState n → TreeState n
  | _, 0, s => s
  | level, d + 1, s => run δ (level + 1) d (round (δ level) s)

/-- Algorithm 1, expanded over the original (indexed) input occurrences. -/
def algorithm (x : List ℝ) (δ : ℕ → ℕ → ℝ) : ℝ :=
  let s := run δ 0 (Nat.clog 2 x.length) (initial x.length)
  ∑ i : Fin x.length, x.get i * s.coeff i

lemma abs_errorAux_le {α : Type} [DecidableEq α] (δ : ℕ → ℝ) (u : ℝ)
    (hδ : ∀ k, |δ k| ≤ u) (k : ℕ) (i : α) (as bs : List (List α)) :
    |errorAux δ k i as bs| ≤ u := by
  induction as generalizing k bs with
  | nil => simp [errorAux, abs_nonneg]
  | cons a as ih =>
    cases bs with
    | nil => simp [errorAux, abs_nonneg]
    | cons b bs =>
      simp only [errorAux]
      split
      · exact hδ k
      · exact ih (k + 1) bs

lemma abs_offsetError_le {α : Type} [DecidableEq α] (δ : ℕ → ℝ) (s : List (List α))
    (u : ℝ) (hδ : ∀ k, |δ k| ≤ u) (i : α) : |offsetError δ s i| ≤ u := by
  exact abs_errorAux_le δ u hδ 0 i _ _

lemma gamma_nonneg (k : ℕ) {u : ℝ} (hu : 0 ≤ u) (hsmall : (k : ℝ) * u < 1) :
    0 ≤ gamma k u := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (sub_nonneg.mpr hsmall.le)

lemma gamma_step {k : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (hsmall : ((k + 1 : ℕ) : ℝ) * u < 1) :
    gamma k u + u + gamma k u * u ≤ gamma (k + 1) u := by
  have hk : (k : ℝ) * u < 1 := by
    have hcast : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hu) hsmall
  have hkpos : 0 < 1 - (k : ℝ) * u := sub_pos.mpr hk
  have hspos : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := sub_pos.mpr hsmall
  rw [gamma, gamma]
  apply (div_le_iff₀ hspos).2
  field_simp
  nlinarith [sq_nonneg u]

lemma coeff_step {c e u g : ℝ} (hu : 0 ≤ u) (hc : |c - 1| ≤ g)
    (hg : 0 ≤ g) (he : |e| ≤ u) : |c * (1 + e) - 1| ≤ g + u + g * u := by
  calc
    |c * (1 + e) - 1| = |(c - 1) + e + (c - 1) * e| := by ring_nf
    _ ≤ |c - 1| + |e| + |c - 1| * |e| := by
      calc
        _ ≤ |c - 1| + |e| + |(c - 1) * e| := abs_add_three _ _ _
        _ = _ := by rw [abs_mul]
    _ ≤ g + u + g * u := by gcongr

lemma run_coeff_bound {n : ℕ} (δ : ℕ → ℕ → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hδ : ∀ l k, |δ l k| ≤ u) (level d : ℕ) (s : TreeState n)
    (hs : ∀ i, |s.coeff i - 1| ≤ gamma level u)
    (hsmall : ((level + d : ℕ) : ℝ) * u < 1) :
    ∀ i, |(run δ level d s).coeff i - 1| ≤ gamma (level + d) u := by
  induction d generalizing level s with
  | zero => simpa using hs
  | succ d ih =>
    simp only [run]
    apply ih (level := level + 1) (s := round (δ level) s)
    · intro i
      apply (coeff_step hu (hs i) (gamma_nonneg level hu ?_)
        (abs_offsetError_le (δ level) s.blocks u (hδ level) i)).trans
      · have hle : (level : ℝ) ≤ ((level + (d + 1) : ℕ) : ℝ) := by norm_num
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle hu) hsmall
      · apply gamma_step hu
        have hle : (((level + 1 : ℕ) : ℝ)) ≤ ((level + (d + 1) : ℕ) : ℝ) := by norm_num
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle hu) hsmall
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsmall

/-- Theorem 3.1. The backward errors are indexed by input occurrence. -/
theorem theorem_3_1 (x : List ℝ) (hne : x ≠ []) (δ : ℕ → ℕ → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hδ : ∀ l k, |δ l k| ≤ u)
    (hsmall : ((Nat.clog 2 x.length : ℕ) : ℝ) * u < 1) :
    ∃ Δ : Fin x.length → ℝ,
      algorithm x δ = ∑ i : Fin x.length, (x.get i + Δ i) ∧
      ∀ i, |Δ i| ≤ gamma (Nat.clog 2 x.length) u * |x.get i| := by
  let depth := Nat.clog 2 x.length
  let final := run δ 0 depth (initial x.length)
  have hcoeff : ∀ i, |final.coeff i - 1| ≤ gamma depth u := by
    apply run_coeff_bound δ u hu hδ 0 depth (initial x.length)
    · intro i
      simp [initial, gamma]
    · simpa [depth] using hsmall
  refine ⟨fun i => x.get i * (final.coeff i - 1), ?_, ?_⟩
  · simp only [algorithm, final, depth]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro i
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hcoeff i) (abs_nonneg _)

end ParallelBinaryTree
