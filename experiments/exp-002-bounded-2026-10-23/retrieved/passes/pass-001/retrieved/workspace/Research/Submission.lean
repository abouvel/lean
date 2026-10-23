import Mathlib

/-! Bhola, Algorithm 1. Zero-based indices are used. `clog` is the ceiling logarithm.
The operation argument models floating-point addition; the carry branch invokes no operation.
-/
namespace Bhola

/-- Pair the first half against the second half, preserving an unmatched suffix unchanged. -/
def pairOffset (op : α → α → α) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | a :: xs, b :: ys => op a b :: pairOffset op xs ys

/-- The split is at ceil(length/2), not at adjacent pairs. -/
def round (op : α → α → α) (xs : List α) : List α :=
  let h := (xs.length + 1) / 2
  pairOffset op (xs.take h) (xs.drop h)

/-- Exactly the prescribed number of parallel rounds. -/
def stages (op : α → α → α) : ℕ → List α → List α
  | 0, xs => xs
  | k + 1, xs => stages op k (round op xs)

def depth (xs : List α) : ℕ := Nat.clog 2 xs.length

def algorithm (op : ℝ → ℝ → ℝ) (xs : List ℝ) : ℝ :=
  (stages op (depth xs) xs).headD 0

/-- Standard relative-error model. No rounding is performed by a carry. -/
def RoundingModel (op : ℝ → ℝ → ℝ) (u : ℝ) : Prop :=
  ∀ a b, ∃ δ : ℝ, |δ| ≤ u ∧ op a b = (a + b) * (1 + δ)

noncomputable def gamma (k : ℕ) (u : ℝ) : ℝ := (k : ℝ) * u / (1 - (k : ℝ) * u)

 theorem pairOffset_length (op : α → α → α) (xs ys : List α) :
    (pairOffset op xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [pairOffset]
  | cons a xs ih =>
    cases ys with
    | nil => simp [pairOffset]
    | cons b ys => simp [pairOffset, ih, Nat.succ_max_succ]

 theorem round_length (op : α → α → α) (xs : List α) :
    (round op xs).length = (xs.length + 1) / 2 := by
  simp only [round, pairOffset_length, List.length_take, List.length_drop]
  have h : (xs.length + 1) / 2 ≤ xs.length := by omega
  rw [min_eq_left h, max_eq_left]
  omega

 theorem stages_length_le (op : α → α → α) (k : ℕ) (xs : List α)
    (h : xs.length ≤ 2 ^ k) : (stages op k xs).length ≤ 1 := by
  induction k generalizing xs with
  | zero => simpa [stages] using h
  | succ k ih =>
    apply ih
    rw [round_length]
    rw [pow_succ] at h
    omega

 theorem round_nonempty (op : α → α → α) (xs : List α) (h : xs ≠ []) :
    round op xs ≠ [] := by
  have hp : 0 < xs.length := List.length_pos_iff.mpr h
  have : 0 < (round op xs).length := by rw [round_length]; omega
  exact List.length_pos_iff.mp this

 theorem stages_nonempty (op : α → α → α) (k : ℕ) (xs : List α) (h : xs ≠ []) :
    stages op k xs ≠ [] := by
  induction k generalizing xs with
  | zero => exact h
  | succ k ih => exact ih _ (round_nonempty op xs h)

/-- The logarithmic schedule produces exactly one result for every nonempty input. -/
 theorem final_length (op : α → α → α) (xs : List α) (h : xs ≠ []) :
    (stages op (depth xs) xs).length = 1 := by
  have hle := stages_length_le op (depth xs) xs
    ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp (le_refl (depth xs)))
  have hp := List.length_pos_iff.mpr (stages_nonempty op (depth xs) xs h)
  omega

 theorem pairOffset_sum (xs ys : List ℝ) :
    (pairOffset (· + ·) xs ys).sum = xs.sum + ys.sum := by
  induction xs generalizing ys with
  | nil => simp [pairOffset]
  | cons a xs ih =>
    cases ys with
    | nil => simp [pairOffset]
    | cons b ys => simp only [pairOffset, List.sum_cons, ih]; ring

 theorem round_sum (xs : List ℝ) : (round (· + ·) xs).sum = xs.sum := by
  rw [round, pairOffset_sum, ← List.sum_append, List.take_append_drop]

 theorem stages_sum (k : ℕ) (xs : List ℝ) :
    (stages (· + ·) k xs).sum = xs.sum := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih => rw [stages, ih, round_sum]

/-- Algorithm 1 computes the exact sum when its additions are exact. -/
 theorem algorithm_exact (xs : List ℝ) (h : xs ≠ []) :
    algorithm (· + ·) xs = xs.sum := by
  have hl := final_length (· + ·) xs h
  have hs := stages_sum (depth xs) xs
  unfold algorithm
  cases he : stages (· + ·) (depth xs) xs with
  | nil => simp [he] at hl
  | cons a as =>
    have ha : as = [] := by simpa [he] using hl
    simpa [he, ha] using hs

/-- Conservation of any additive mass, including a multiset of occurrence labels. -/
theorem pairOffset_mass {M : Type*} [AddCommMonoid M]
    (op : α → α → α) (mass : α → M)
    (hm : ∀ a b, mass (op a b) = mass a + mass b) (xs ys : List α) :
    ((pairOffset op xs ys).map mass).sum =
      (xs.map mass).sum + (ys.map mass).sum := by
  induction xs generalizing ys with
  | nil => simp [pairOffset]
  | cons a xs ih =>
    cases ys with
    | nil => simp [pairOffset]
    | cons b ys =>
      simp [pairOffset, hm, ih, add_assoc, add_left_comm, add_comm]

theorem round_mass {M : Type*} [AddCommMonoid M]
    (op : α → α → α) (mass : α → M)
    (hm : ∀ a b, mass (op a b) = mass a + mass b) (xs : List α) :
    ((round op xs).map mass).sum = (xs.map mass).sum := by
  rw [round, pairOffset_mass op mass hm, ← List.sum_append, ← List.map_append,
    List.take_append_drop]

theorem stages_mass {M : Type*} [AddCommMonoid M]
    (op : α → α → α) (mass : α → M)
    (hm : ∀ a b, mass (op a b) = mass a + mass b) (k : ℕ) (xs : List α) :
    ((stages op k xs).map mass).sum = (xs.map mass).sum := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih => rw [stages, ih, round_mass op mass hm]

/-- Labels travel alongside values. Equal real values still have distinct occurrence labels. -/
def taggedAdd (op : ℝ → ℝ → ℝ) (a b : ℝ × Multiset ℕ) : ℝ × Multiset ℕ :=
  (op a.1 b.1, a.2 + b.2)

/-- Every occurrence label is preserved, with multiplicity, through every round. -/
theorem occurrences_preserved (op : ℝ → ℝ → ℝ) (k : ℕ)
    (xs : List (ℝ × Multiset ℕ)) :
    ((stages (taggedAdd op) k xs).map Prod.snd).sum = (xs.map Prod.snd).sum :=
  stages_mass (taggedAdd op) Prod.snd (by intros; rfl) k xs

/-- A carry is literally unchanged, even for an inexact addition operation. -/
theorem carry_unchanged (op : α → α → α) (xs : List α) :
    pairOffset op xs [] = xs := by cases xs <;> rfl

/-- The schedule is the least integer depth whose binary capacity covers the input. -/
theorem depth_le_iff (xs : List α) (k : ℕ) :
    depth xs ≤ k ↔ xs.length ≤ 2 ^ k :=
  Nat.clog_le_iff_le_pow (by decide)

/-- Local absolute error follows directly from the paper's relative-error model. -/
theorem local_error (op : ℝ → ℝ → ℝ) (u : ℝ) (hm : RoundingModel op u)
    (a b : ℝ) : |op a b - (a + b)| ≤ u * |a + b| := by
  obtain ⟨δ, hd, he⟩ := hm a b
  rw [he]
  have heq : (a + b) * (1 + δ) - (a + b) = δ * (a + b) := by ring
  rw [heq, abs_mul]
  exact mul_le_mul_of_nonneg_right hd (abs_nonneg _)

/-- The full requested componentwise assertion, without assuming distinct input values. -/
def BackwardStable (op : ℝ → ℝ → ℝ) (u : ℝ) (xs : List ℝ) : Prop :=
  ∃ Δ : Fin xs.length → ℝ,
    algorithm op xs = ∑ i : Fin xs.length, (xs.get i + Δ i) ∧
    ∀ i, |Δ i| ≤ gamma (depth xs) u * |xs.get i|

end Bhola
