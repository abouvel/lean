import Mathlib

/-! Algorithm 1 uses offset pairing, not adjacent pairing.  The right half may
be shorter; `pair` returns the remaining left entries without an operation. -/
namespace Bhola

def pair (op : α → α → α) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => op x y :: pair op xs ys

def round (op : α → α → α) (xs : List α) : List α :=
  let m := (xs.length + 1) / 2
  pair op (xs.take m) (xs.drop m)

def levels (op : α → α → α) : ℕ → List α → List α
  | 0, xs => xs
  | k + 1, xs => levels op k (round op xs)

/-- The exact integer ceiling of log₂ n, including the singleton case. -/
def depth (n : ℕ) : ℕ := Nat.clog 2 n

def algorithm (add : ℝ → ℝ → ℝ) (xs : List ℝ) : List ℝ :=
  levels add (depth xs.length) xs

theorem pair_length (op : α → α → α) (xs ys : List α) :
    (pair op xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [pair]
  | cons x xs ih =>
    cases ys with
    | nil => simp [pair]
    | cons y ys => simp [pair, ih, max_add_add_right]

theorem round_length (op : α → α → α) (xs : List α) :
    (round op xs).length = (xs.length + 1) / 2 := by
  rw [round, pair_length, List.length_take, List.length_drop]
  omega

/-- Offset pairing preserves every additive observable.  In particular, take
`measure` to count any chosen input occurrence in a list of occurrence labels. -/
theorem pair_measure {M : Type*} [AddCommMonoid M]
    (op : α → α → α) (measure : α → M)
    (hop : ∀ x y, measure (op x y) = measure x + measure y)
    (xs ys : List α) :
    ((pair op xs ys).map measure).sum =
      (xs.map measure).sum + (ys.map measure).sum := by
  induction xs generalizing ys with
  | nil => simp [pair]
  | cons x xs ih =>
    cases ys with
    | nil => simp [pair]
    | cons y ys => simp [pair, hop, ih, add_assoc, add_left_comm]

theorem round_measure {M : Type*} [AddCommMonoid M]
    (op : α → α → α) (measure : α → M)
    (hop : ∀ x y, measure (op x y) = measure x + measure y)
    (xs : List α) :
    ((round op xs).map measure).sum = (xs.map measure).sum := by
  rw [round, pair_measure op measure hop, ← List.sum_append, ← List.map_append,
    List.take_append_drop]

theorem levels_measure {M : Type*} [AddCommMonoid M]
    (op : α → α → α) (measure : α → M)
    (hop : ∀ x y, measure (op x y) = measure x + measure y)
    (k : ℕ) (xs : List α) :
    ((levels op k xs).map measure).sum = (xs.map measure).sum := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih => rw [levels, ih, round_measure op measure hop]

theorem levels_length_bound (op : α → α → α) (k : ℕ) (xs : List α)
    (h : xs.length ≤ 2 ^ k) : (levels op k xs).length ≤ 1 := by
  induction k generalizing xs with
  | zero => simpa [levels] using h
  | succ k ih =>
    apply ih
    rw [round_length]
    rw [pow_succ] at h
    omega

theorem levels_nonempty (op : α → α → α) (k : ℕ) (xs : List α)
    (h : 0 < xs.length) : 0 < (levels op k xs).length := by
  induction k generalizing xs with
  | zero => exact h
  | succ k ih =>
    apply ih
    rw [round_length]
    omega

theorem algorithm_length (add : ℝ → ℝ → ℝ) (xs : List ℝ)
    (h : xs ≠ []) : (algorithm add xs).length = 1 := by
  have hp : 0 < xs.length := List.length_pos_iff.mpr h
  have h₁ := levels_length_bound add (depth xs.length) xs
    (Nat.le_pow_clog (by decide : 1 < 2) xs.length)
  have h₂ := levels_nonempty add (depth xs.length) xs hp
  unfold algorithm
  omega

theorem depth_minimal (n k : ℕ) : depth n ≤ k ↔ n ≤ 2 ^ k := by
  exact Nat.clog_le_iff_le_pow (by decide)

/-- With real addition Algorithm 1 returns the exact sum. -/
theorem exact_sum (xs : List ℝ) : (algorithm (· + ·) xs).sum = xs.sum := by
  simpa [algorithm] using
    levels_measure (α := ℝ) (M := ℝ) (· + ·) id (by intros; rfl)
      (depth xs.length) xs

/-- Each occurrence can be given its original position as a label.  Counting
any label after reduction gives exactly its initial multiplicity. -/
theorem occurrence_count [DecidableEq α] (label : α) (k : ℕ)
    (blocks : List (List α)) :
    (((levels (· ++ ·) k blocks).map (List.count label)).sum) =
      ((blocks.map (List.count label)).sum) := by
  apply levels_measure
  intro x y
  simp

/-- In particular, no input occurrence disappears or is duplicated when the
initial blocks are singletons, even if the input values happen to coincide. -/
theorem singleton_occurrences [DecidableEq α] (label : α) (k : ℕ)
    (xs : List α) :
    (((levels (· ++ ·) k (xs.map List.singleton)).map
      (List.count label)).sum) = xs.count label := by
  rw [occurrence_count]
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons] at *
    rw [ih]
    by_cases h : x = label
    · subst x; simp [List.singleton, Nat.add_comm]
    · simp [List.singleton, h]

/-- Standard relative-error model, with no rounding on the carry branch. -/
def StandardModel (add : ℝ → ℝ → ℝ) (u : ℝ) : Prop :=
  0 ≤ u ∧ ∀ a b, ∃ δ : ℝ, |δ| ≤ u ∧ add a b = (a + b) * (1 + δ)

noncomputable def gamma (k : ℕ) (u : ℝ) : ℝ := (k : ℝ) * u / (1 - (k : ℝ) * u)

theorem gamma_step (n : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (h : ((n : ℝ) + 1) * u < 1) :
    gamma n u * (1 + u) + u ≤ gamma (n + 1) u := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h₀ : 0 < 1 - (n : ℝ) * u := by nlinarith
  have h₁ : 0 < 1 - ((n : ℝ) + 1) * u := by linarith
  unfold gamma
  push_cast
  apply (le_div_iff₀ h₁).2
  field_simp [ne_of_gt h₀]
  nlinarith [sq_nonneg u, mul_nonneg hn hu]

/-- The scalar product estimate used on each leaf-to-root path. -/
theorem path_error (ds : List ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hd : ∀ d ∈ ds, |d| ≤ u) (h : (ds.length : ℝ) * u < 1) :
    |(ds.map (1 + ·)).prod - 1| ≤ gamma ds.length u := by
  induction ds with
  | nil => simp [gamma]
  | cons d ds ih =>
    have hd₀ := hd d (by simp)
    have ht : (ds.length : ℝ) * u < 1 := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
      nlinarith
    have hi := ih (by intro e he; exact hd e (by simp [he])) ht
    have hp : |1 + d| ≤ 1 + u := by
      calc
        |1 + d| ≤ |(1 : ℝ)| + |d| := abs_add_le _ _
        _ ≤ 1 + u := by simpa using hd₀
    have hg : 0 ≤ gamma ds.length u := by
      unfold gamma
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    calc
      |(1 + d) * (ds.map (1 + ·)).prod - 1| =
          |(1 + d) * ((ds.map (1 + ·)).prod - 1) + d| := by congr 1; ring
      _ ≤ |1 + d| * |(ds.map (1 + ·)).prod - 1| + |d| := by
        simpa [abs_mul] using
          (abs_add_le ((1 + d) * ((ds.map (1 + ·)).prod - 1)) d)
      _ ≤ (1 + u) * gamma ds.length u + u := by
        gcongr
      _ ≤ gamma (ds.length + 1) u := by
        rw [mul_comm]
        exact gamma_step ds.length u hu (by simpa using h)

/-- The complete target statement, kept separate from the proved algorithmic
facts.  Perturbations are aligned by list position, so repeated values remain
separate occurrences. -/
def BackwardStable (add : ℝ → ℝ → ℝ) (u : ℝ) (xs : List ℝ) : Prop :=
  ∃ perturb : Fin xs.length → ℝ,
    (algorithm add xs).sum =
      ∑ i : Fin xs.length, (xs[i] + perturb i) ∧
    ∀ i : Fin xs.length,
      |perturb i| ≤ gamma (depth xs.length) u * |xs[i]|

end Bhola
