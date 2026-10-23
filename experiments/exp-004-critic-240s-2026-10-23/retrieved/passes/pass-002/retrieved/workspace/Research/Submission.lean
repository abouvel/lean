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
def Tree.eval (δ : List Bool → ℝ) : Tree → ℝ
  | .leaf x => x
  | .node a b => (a.eval (fun p => δ (false :: p)) + b.eval (fun p => δ (true :: p))) * (1 + δ [])

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

def computed (δ : List Bool → ℝ) (xs : List ℝ) : ℝ :=
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
noncomputable def Tree.paths (δ : List Bool → ℝ) : Tree → List (ℝ × List ℝ)
  | .leaf x => [(x, [])]
  | .node a b => (a.paths (fun p => δ (false :: p)) ++ b.paths (fun p => δ (true :: p))).map
      (fun p => (p.1, δ [] :: p.2))

theorem paths_occurrences (δ : List Bool → ℝ) (t : Tree) :
    ((t.paths δ).map Prod.fst : Multiset ℝ) = t.leaves := by
  induction t generalizing δ with
  | leaf x => simp [Tree.paths, Tree.leaves]
  | node a b ha hb => simpa [Tree.paths, Tree.leaves, List.map_map, Function.comp_def] using congrArg₂ (· + ·) (ha _) (hb _)

theorem paths_length (δ : List Bool → ℝ) (t : Tree) :
    ∀ p ∈ t.paths δ, p.2.length ≤ t.depth := by
  induction t generalizing δ with
  | leaf x => simp [Tree.paths, Tree.depth]
  | node a b ha hb =>
    intro p hp
    simp only [Tree.paths, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩
    simp only [List.mem_append] at hq
    simp only [List.length_cons, Tree.depth]
    rcases hq with hq | hq
    · exact Nat.add_le_add_right ((ha _ q hq).trans (le_max_left _ _)) 1
    · exact Nat.add_le_add_right ((hb _ q hq).trans (le_max_right _ _)) 1

noncomputable def term (p : ℝ × List ℝ) : ℝ :=
  p.1 * (p.2.map (fun e => 1 + e)).prod

theorem paths_evaluate (δ : List Bool → ℝ) (t : Tree) :
    t.eval δ = ((t.paths δ).map term).sum := by
  induction t generalizing δ with
  | leaf x => simp [Tree.eval, Tree.paths, term]
  | node a b ha hb =>
    have hm : ∀ ps : List (ℝ × List ℝ),
        (ps.map (fun p => term (p.1, δ [] :: p.2))).sum =
          (ps.map term).sum * (1 + δ []) := by
      intro ps
      induction ps with
      | nil => simp
      | cons p ps ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        have ht : term (p.1, δ [] :: p.2) = term p * (1 + δ []) := by
          simp only [term, List.map_cons, List.prod_cons]
          ring
        rw [ht, add_mul]
    simpa [Tree.eval, Tree.paths, List.map_map, Function.comp_def, List.map_append,
      List.sum_append, ha, hb] using (hm (a.paths (fun p => δ (false :: p)) ++ b.paths (fun p => δ (true :: p)))).symm

theorem paths_errors (δ : List Bool → ℝ) (u : ℝ) (h : ∀ t, |δ t| ≤ u) (t : Tree) :
    ∀ p ∈ t.paths δ, ∀ e ∈ p.2, |e| ≤ u := by
  induction t generalizing δ with
  | leaf x => simp [Tree.paths]
  | node a b ha hb =>
    intro p hp e he
    simp only [Tree.paths, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact h _
    · rcases List.mem_append.mp hq with hq | hq
      · exact ha _ (fun p => h _) q hq e he
      · exact hb _ (fun p => h _) q hq e he

/-- Bounded product estimate, including paths shorter than the maximum depth. -/
theorem product_bound (es : List ℝ) (u : ℝ) (hu : 0 ≤ u)
    (he : ∀ e ∈ es, |e| ≤ u) (hd : (es.length : ℝ) * u < 1) :
    |(es.map (fun e => 1 + e)).prod - 1| ≤ gamma es.length u := by
  induction es with
  | nil => simp [gamma]
  | cons e es ih =>
    have he0 := he e (by simp)
    have hes : ∀ a ∈ es, |a| ≤ u := fun a ha => he a (by simp [ha])
    have hc : ((e :: es).length : ℝ) = (es.length : ℝ) + 1 := by simp
    rw [hc] at hd
    have ht : (es.length : ℝ) * u < 1 := by nlinarith
    have hi := ih hes ht
    let P := (es.map (fun e => 1 + e)).prod
    have hp : |P - 1| ≤ (es.length : ℝ) * u / (1 - (es.length : ℝ) * u) := hi
    have hstep : |(1 + e) * P - 1| ≤ |P - 1| * (1 + u) + u := by
      have hid : (1 + e) * P - 1 = (P - 1) * (1 + e) + e := by ring
      rw [hid]
      calc
        _ ≤ |(P - 1) * (1 + e)| + |e| := abs_add_le _ _
        _ = |P - 1| * |1 + e| + |e| := by rw [abs_mul]
        _ ≤ |P - 1| * (1 + u) + u := by
          gcongr
          calc
            |1 + e| ≤ |(1 : ℝ)| + |e| := abs_add_le _ _
            _ ≤ 1 + u := by simpa using he0
    have hpos : 0 < 1 - (es.length : ℝ) * u := by linarith
    have hpos' : 0 < 1 - ((es.length : ℝ) + 1) * u := by linarith
    have hrat : ((es.length : ℝ) * u / (1 - (es.length : ℝ) * u)) * (1 + u) + u ≤
        ((es.length : ℝ) + 1) * u / (1 - ((es.length : ℝ) + 1) * u) := by
      apply (le_div_iff₀ hpos').2
      apply (mul_le_mul_iff_left₀ hpos).mp
      field_simp
      nlinarith [sq_nonneg u, mul_nonneg (by positivity : (0 : ℝ) ≤ es.length) (sq_nonneg u)]
    change |(1 + e) * P - 1| ≤ _
    simp only [gamma, hc]
    apply hstep.trans
    apply le_trans _ hrat
    gcongr

theorem gamma_mono {k d : ℕ} {u : ℝ} (hu : 0 ≤ u) (hk : k ≤ d)
    (hd : (d : ℝ) * u < 1) : gamma k u ≤ gamma d u := by
  have hku : (k : ℝ) * u ≤ (d : ℝ) * u := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hu
  unfold gamma
  apply div_le_div₀ (by positivity) hku (by linarith) (by linarith)

/-- Theorem 3.1: perturbations are returned in the original input order.
Every addition has its own address-indexed error; carries have no error. -/
theorem theorem_3_1 (xs : List ℝ) (hn : xs ≠ []) (δ : List Bool → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (he : ∀ address, |δ address| ≤ u)
    (hd : (Nat.clog 2 xs.length : ℝ) * u < 1) :
    ∃ perturbations : List (ℝ × ℝ),
      perturbations.map Prod.fst = xs ∧
      computed δ xs = (perturbations.map (fun p => p.1 + p.2)).sum ∧
      ∀ p ∈ perturbations, |p.2| ≤ gamma (Nat.clog 2 xs.length) u * |p.1| := by
  obtain ⟨t, ht⟩ := algorithm_singleton xs hn
  let ps := t.paths δ
  have hp : (ps.map Prod.fst : Multiset ℝ) = (xs : Multiset ℝ) := by
    rw [paths_occurrences]
    have hh := all_occurrences xs
    simpa [ht] using hh
  have hperm : xs.Perm (ps.map Prod.fst) := by
    exact (Quotient.exact hp).symm
  have hx : Relation.Comp (fun a b => a = List.map Prod.fst b) List.Perm xs ps :=
    (congrFun (congrFun (List.eq_map_comp_perm Prod.fst) xs) ps).mpr hperm
  obtain ⟨qs, hqs, hqp⟩ := hx
  have hdepth := logarithmic_depth xs t (by simp [ht])
  have hb : ∀ p ∈ qs, |(p.2.map (fun e => 1 + e)).prod - 1| ≤
      gamma (Nat.clog 2 xs.length) u := by
    intro p hp
    have hmem : p ∈ t.paths δ := hqp.mem_iff.mp hp
    have hl := (paths_length δ t p hmem).trans hdepth
    have hlu : (p.2.length : ℝ) * u ≤ (Nat.clog 2 xs.length : ℝ) * u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hu
    exact (product_bound p.2 u hu (paths_errors δ u he t p hmem) (by linarith)).trans
      (gamma_mono hu hl hd)
  refine ⟨qs.map (fun p => (p.1, p.1 * ((p.2.map (fun e => 1 + e)).prod - 1))), ?_, ?_, ?_⟩
  · simpa [List.map_map, Function.comp_def] using hqs.symm
  · have hv : computed δ xs = (ps.map term).sum := by
      simp [computed, ht, ps, paths_evaluate]
    rw [hv, ← hqp.map term |>.sum_eq]
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro p _
    dsimp [Function.comp_def, term]
    ring
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    dsimp
    rw [abs_mul]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hb q hq) (abs_nonneg q.1)

end Bhola

namespace Bhola
example : ((rounds 1 ([2,3,4,5,6].map Tree.leaf)).map (Tree.eval (fun _ => 0))) = [7,9,4] := by
  norm_num [rounds, round, pair, Tree.eval]
example : ((rounds 2 ([2,3,4,5,6].map Tree.leaf)).map (Tree.eval (fun _ => 0))) = [11,9] := by
  norm_num [rounds, round, pair, Tree.eval]
example : ((rounds 3 ([2,3,4,5,6].map Tree.leaf)).map (Tree.eval (fun _ => 0))) = [20] := by
  norm_num [rounds, round, pair, Tree.eval]
example (x : ℝ) (δ : List Bool → ℝ) : computed δ [x] = x := by
  simp [computed, algorithm, rounds, Nat.clog, Tree.eval]
example : forestLeaves (rounds 3 ([2,2,2,2,2].map Tree.leaf)) =
    ((([2,2,2,2,2] : List ℝ) : Multiset ℝ)) := by
  rw [rounds_leaves]
  simp [forestLeaves, Tree.leaves]
end Bhola
