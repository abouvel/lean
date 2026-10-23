import Mathlib

/-! Algorithm 1: zero-based offset pairing, with a genuinely unchanged carry.
`Nat.clog 2 n` is the least d such that n ≤ 2^d, i.e. ceil(log₂ n).
The trees retain every input occurrence, including repeated real values. -/
namespace Bhola
inductive Tree where
  | leaf : ℝ → Tree
  | node : Tree → Tree → Tree
  deriving Inhabited

def Tree.leaves : Tree → Multiset ℝ
  | .leaf x => {x}
  | .node a b => a.leaves + b.leaves

def Tree.depth : Tree → ℕ
  | .leaf _ => 0
  | .node a b => max a.depth b.depth + 1

/-- A separate error is allowed at every actual addition. No rounding occurs on a carry. -/
def Tree.eval (δ : Tree → ℝ) : Tree → ℝ
  | .leaf x => x
  | .node a b => (a.eval δ + b.eval δ) * (1 + δ (.node a b))

def pair : List Tree → List Tree → List Tree
  | [], ys => ys
  | xs, [] => xs
  | a :: xs, b :: ys => .node a b :: pair xs ys

/-- The offset is ceil(current length / 2); the right half is paired with
 the left half, and the excess left element is carried without an addition. -/
def round (xs : List Tree) : List Tree :=
  let m := (xs.length + 1) / 2
  pair (xs.take m) (xs.drop m)

def rounds : ℕ → List Tree → List Tree
  | 0, xs => xs
  | d + 1, xs => rounds d (round xs)

def forestLeaves (xs : List Tree) : Multiset ℝ := (xs.map Tree.leaves).sum

def algorithm (xs : List ℝ) : List Tree :=
  rounds (Nat.clog 2 xs.length) (xs.map Tree.leaf)

def computed (δ : Tree → ℝ) (xs : List ℝ) : ℝ :=
  ((algorithm xs).map (Tree.eval δ)).sum

@[simp] theorem forest_nil : forestLeaves [] = 0 := rfl
@[simp] theorem forest_cons (x : Tree) (xs : List Tree) :
    forestLeaves (x :: xs) = x.leaves + forestLeaves xs := by simp [forestLeaves]

theorem forest_append (xs ys : List Tree) :
    forestLeaves (xs ++ ys) = forestLeaves xs + forestLeaves ys := by
  simp [forestLeaves]

theorem pair_leaves (xs ys : List Tree) :
    forestLeaves (pair xs ys) = forestLeaves xs + forestLeaves ys := by
  induction xs generalizing ys with
  | nil => simp [pair]
  | cons x xs ih =>
    cases ys with
    | nil => simp [pair]
    | cons y ys => simp [pair, Tree.leaves, ih, add_assoc, add_comm, add_left_comm]

theorem round_leaves (xs : List Tree) : forestLeaves (round xs) = forestLeaves xs := by
  rw [round, pair_leaves, ← forest_append, List.take_append_drop]

theorem rounds_leaves (d : ℕ) (xs : List Tree) :
    forestLeaves (rounds d xs) = forestLeaves xs := by
  induction d generalizing xs with
  | zero => rfl
  | succ d ih => rw [rounds, ih, round_leaves]

/-- Multiset equality preserves multiplicity, not merely membership. -/
theorem all_occurrences (xs : List ℝ) : forestLeaves (algorithm xs) = (xs : Multiset ℝ) := by
  rw [algorithm, rounds_leaves]
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [Tree.leaves] using congrArg (fun s => ({x} : Multiset ℝ) + s) ih

theorem pair_length (xs ys : List Tree) : (pair xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [pair]
  | cons x xs ih =>
    cases ys with
    | nil => simp [pair]
    | cons y ys => simp [pair, ih, Nat.succ_max_succ]

theorem round_length (xs : List Tree) : (round xs).length = (xs.length + 1) / 2 := by
  simp only [round, pair_length, List.length_take, List.length_drop]
  omega

theorem rounds_length_le (d : ℕ) (xs : List Tree) (h : xs.length ≤ 2^d) :
    (rounds d xs).length ≤ 1 := by
  induction d generalizing xs with
  | zero => simpa [rounds] using h
  | succ d ih =>
    apply ih
    rw [round_length]
    rw [pow_succ] at h
    omega

theorem rounds_nonempty (d : ℕ) (xs : List Tree) (h : xs ≠ []) : rounds d xs ≠ [] := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    apply ih
    intro he
    have hl := round_length xs
    rw [he] at hl
    have hp : 0 < xs.length := List.length_pos_iff.mpr h
    simp only [List.length_nil] at hl
    omega

theorem algorithm_singleton (xs : List ℝ) (h : xs ≠ []) : ∃ t, algorithm xs = [t] := by
  have hl : (algorithm xs).length ≤ 1 :=
    rounds_length_le _ _ (by simpa using Nat.le_pow_clog (by decide : 1 < 2) xs.length)
  have hn : algorithm xs ≠ [] := rounds_nonempty _ _ (by simpa using h)
  cases he : algorithm xs with
  | nil => exact False.elim (hn he)
  | cons t ts =>
    cases ts with
    | nil => exact ⟨t, rfl⟩
    | cons a as => simp [he] at hl

theorem pair_depth (xs ys : List Tree) (d : ℕ)
    (hx : ∀ t ∈ xs, t.depth ≤ d) (hy : ∀ t ∈ ys, t.depth ≤ d) :
    ∀ t ∈ pair xs ys, t.depth ≤ d + 1 := by
  induction xs generalizing ys with
  | nil => simpa [pair] using fun t ht => Nat.le_succ_of_le (hy t ht)
  | cons x xs ih =>
    cases ys with
    | nil => simpa [pair] using fun t ht => Nat.le_succ_of_le (hx t ht)
    | cons y ys =>
      intro t ht
      simp only [pair, List.mem_cons] at ht
      rcases ht with rfl | ht
      · simp only [Tree.depth, Nat.add_le_add_iff_right, max_le_iff]
        exact ⟨hx x (by simp), hy y (by simp)⟩
      · exact ih ys (fun t ht => hx t (by simp [ht]))
          (fun t ht => hy t (by simp [ht])) t ht

theorem round_depth (xs : List Tree) (d : ℕ) (h : ∀ t ∈ xs, t.depth ≤ d) :
    ∀ t ∈ round xs, t.depth ≤ d + 1 := by
  apply pair_depth
  · exact fun t ht => h t (List.mem_of_mem_take ht)
  · exact fun t ht => h t (List.mem_of_mem_drop ht)

theorem rounds_depth (k d : ℕ) (xs : List Tree) (h : ∀ t ∈ xs, t.depth ≤ d) :
    ∀ t ∈ rounds k xs, t.depth ≤ d + k := by
  induction k generalizing d xs with
  | zero => simpa [rounds] using h
  | succ k ih =>
    simpa [rounds, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (d + 1) (round xs) (round_depth xs d h)

theorem logarithmic_depth (xs : List ℝ) :
    ∀ t ∈ algorithm xs, t.depth ≤ Nat.clog 2 xs.length := by
  change ∀ t ∈ rounds (Nat.clog 2 xs.length) (xs.map Tree.leaf), t.depth ≤ Nat.clog 2 xs.length
  simpa using rounds_depth (Nat.clog 2 xs.length) 0 (xs.map Tree.leaf) (by
    intro t ht
    rcases List.mem_map.mp ht with ⟨x, _, rfl⟩
    simp [Tree.depth])

@[simp] theorem exact_tree (t : Tree) : t.eval (fun _ => 0) = t.leaves.sum := by
  induction t with
  | leaf x => simp [Tree.eval, Tree.leaves]
  | node a b ha hb => simp [Tree.eval, Tree.leaves, ha, hb]

theorem exact_sum (xs : List ℝ) : computed (fun _ => 0) xs = xs.sum := by
  have hf : ∀ ts : List Tree, (ts.map (Tree.eval (fun _ => 0))).sum = (forestLeaves ts).sum := by
    intro ts
    induction ts with
    | nil => simp [forestLeaves]
    | cons t ts ih => simp [ih]
  rw [computed, hf, all_occurrences]
  rfl

/-- The problem-size dependent constant used in Theorem 3.1. -/
noncomputable def gamma (d : ℕ) (u : ℝ) : ℝ := (d : ℝ) * u / (1 - (d : ℝ) * u)

/-- Each occurrence is equipped with precisely the errors on its path;
 carried nodes introduce no factor. -/
noncomputable def Tree.paths (δ : Tree → ℝ) : Tree → List (ℝ × List ℝ)
  | .leaf x => [(x, [])]
  | .node a b => (a.paths δ ++ b.paths δ).map
      (fun p => (p.1, δ (.node a b) :: p.2))

theorem paths_occurrences (δ : Tree → ℝ) (t : Tree) :
    ((t.paths δ).map Prod.fst : Multiset ℝ) = t.leaves := by
  induction t with
  | leaf x => simp [Tree.paths, Tree.leaves]
  | node a b ha hb => simpa [Tree.paths, Tree.leaves, List.map_map, Function.comp_def] using congrArg₂ (· + ·) ha hb

theorem paths_length (δ : Tree → ℝ) (t : Tree) :
    ∀ p ∈ t.paths δ, p.2.length ≤ t.depth := by
  induction t with
  | leaf x => simp [Tree.paths, Tree.depth]
  | node a b ha hb =>
    intro p hp
    simp only [Tree.paths, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩
    simp only [List.mem_append] at hq
    simp only [List.length_cons, Tree.depth]
    rcases hq with hq | hq
    · exact Nat.add_le_add_right ((ha q hq).trans (le_max_left _ _)) 1
    · exact Nat.add_le_add_right ((hb q hq).trans (le_max_right _ _)) 1

noncomputable def term (p : ℝ × List ℝ) : ℝ :=
  p.1 * (p.2.map (fun e => 1 + e)).prod

theorem paths_evaluate (δ : Tree → ℝ) (t : Tree) :
    t.eval δ = ((t.paths δ).map term).sum := by
  induction t with
  | leaf x => simp [Tree.eval, Tree.paths, term]
  | node a b ha hb =>
    have hm : ∀ ps : List (ℝ × List ℝ),
        (ps.map (fun p => term (p.1, δ (.node a b) :: p.2))).sum =
          (ps.map term).sum * (1 + δ (.node a b)) := by
      intro ps
      induction ps with
      | nil => simp
      | cons p ps ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        have ht : term (p.1, δ (.node a b) :: p.2) = term p * (1 + δ (.node a b)) := by
          simp only [term, List.map_cons, List.prod_cons]
          ring
        rw [ht, add_mul]
    simpa [Tree.eval, Tree.paths, List.map_map, Function.comp_def, List.map_append,
      List.sum_append, ha, hb] using (hm (a.paths δ ++ b.paths δ)).symm

theorem paths_errors (δ : Tree → ℝ) (u : ℝ) (h : ∀ t, |δ t| ≤ u) (t : Tree) :
    ∀ p ∈ t.paths δ, ∀ e ∈ p.2, |e| ≤ u := by
  induction t with
  | leaf x => simp [Tree.paths]
  | node a b ha hb =>
    intro p hp e he
    simp only [Tree.paths, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact h _
    · rcases List.mem_append.mp hq with hq | hq
      · exact ha q hq e he
      · exact hb q hq e he

end Bhola
