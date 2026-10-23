import Mathlib

/-! Offset-paired binary reduction from Bhola, Algorithm 1.
Input occurrences carry their original indices. A carry creates no rounding node.
The rounding model is represented by an arbitrary error at each addition node.
-/
namespace Bhola

inductive Tree where
  | leaf (index : ℕ) (value : ℝ)
  | add (level slot : ℕ) (left right : Tree)

def Tree.leaves : Tree → List (ℕ × ℝ)
  | .leaf i x => [(i, x)]
  | .add _ _ a b => a.leaves ++ b.leaves

def Tree.height : Tree → ℕ
  | .leaf _ _ => 0
  | .add _ _ a b => max a.height b.height + 1

/-- Pair left slot k with right slot k, whose original offset is the split size.
If the right slot is absent, return the left tree literally unchanged. -/
def pair (level : ℕ) : ℕ → List Tree → List Tree → List Tree
  | _, [], ys => ys
  | _, xs, [] => xs
  | k, a :: as, b :: bs => .add level k a b :: pair level (k + 1) as bs

/-- Ceiling of n / 2^(level+1), using natural-number arithmetic. -/
def offset (n level : ℕ) : ℕ := (n + 2 ^ (level + 1) - 1) / 2 ^ (level + 1)

def step (n level : ℕ) (ts : List Tree) : List Tree :=
  pair level 0 (ts.take (offset n level)) (ts.drop (offset n level))

def rounds (n : ℕ) : ℕ → ℕ → List Tree → List Tree
  | 0, _, ts => ts
  | fuel + 1, level, ts => rounds n fuel (level + 1) (step n level ts)

/-- Nat.clog is the integer ceiling of log base two. -/
def depth (n : ℕ) : ℕ := Nat.clog 2 n

def forest (xs : List ℝ) : List Tree :=
  rounds xs.length (depth xs.length) 0
    (xs.zipIdx.map fun p => Tree.leaf p.2 p.1)

noncomputable def Tree.eval (δ : ℕ → ℕ → ℝ) : Tree → ℝ
  | .leaf _ x => x
  | .add l k a b => (a.eval δ + b.eval δ) * (1 + δ l k)

/-- The algorithm's returned first slot (empty input is assigned zero). -/
noncomputable def algorithm (xs : List ℝ) (δ : ℕ → ℕ → ℝ) : ℝ :=
  match forest xs with
  | [] => 0
  | t :: _ => t.eval δ

/-- Standard relative-error model; carry operations introduce no error. -/
def ValidErrors (u : ℝ) (δ : ℕ → ℕ → ℝ) : Prop :=
  0 ≤ u ∧ ∀ l k, |δ l k| ≤ u

noncomputable def gamma (u : ℝ) (d : ℕ) : ℝ := (d : ℝ) * u / (1 - (d : ℝ) * u)

/-- Every occurrence receives the product of rounding factors on its actual path.
Carries therefore contribute no fictitious rounding factor. -/
noncomputable def Tree.terms (δ : ℕ → ℕ → ℝ) : Tree → List ((ℕ × ℝ) × ℝ)
  | .leaf i x => [((i, x), 1)]
  | .add l k a b => ((a.terms δ ++ b.terms δ).map
      fun p => (p.1, p.2 * (1 + δ l k)))

 theorem terms_occurrences (t : Tree) (δ : ℕ → ℕ → ℝ) :
    (t.terms δ).map Prod.fst = t.leaves := by
  induction t with
  | leaf i x => rfl
  | add l k a b ha hb => simpa [Tree.terms, Tree.leaves, List.map_map,
      Function.comp_def] using congrArg₂ List.append ha hb

 theorem eval_expansion (t : Tree) (δ : ℕ → ℕ → ℝ) :
    t.eval δ = ((t.terms δ).map fun p => p.1.2 * p.2).sum := by
  induction t with
  | leaf i x => simp [Tree.eval, Tree.terms]
  | add l k a b ha hb =>
    simp only [Tree.eval, Tree.terms, List.map_map, List.map_append,
      List.sum_append, Function.comp_def]
    simp_rw [← mul_assoc]
    rw [List.sum_map_mul_right, List.sum_map_mul_right, ← ha, ← hb, add_mul]

/-- A round conserves the multiset of input occurrences, including duplicates. -/
theorem pair_occurrences (l k : ℕ) (as bs : List Tree) :
    ((pair l k as bs).flatMap Tree.leaves).Perm
      (as.flatMap Tree.leaves ++ bs.flatMap Tree.leaves) := by
  induction as generalizing k bs with
  | nil => simp [pair]
  | cons a as ih =>
    cases bs with
    | nil => simp [pair]
    | cons b bs =>
      have h₁ := (ih (k+1) bs).append_left (a.leaves ++ b.leaves)
      have h₂ := ((List.perm_append_comm (l₁ := b.leaves)
        (l₂ := as.flatMap Tree.leaves)).append_right (bs.flatMap Tree.leaves)).append_left a.leaves
      simpa [pair, Tree.leaves, List.flatMap_cons, List.append_assoc] using
        h₁.trans (by simpa [List.append_assoc] using h₂)

theorem step_occurrences (n l : ℕ) (ts : List Tree) :
    ((step n l ts).flatMap Tree.leaves).Perm (ts.flatMap Tree.leaves) := by
  have h := pair_occurrences l 0 (ts.take (offset n l)) (ts.drop (offset n l))
  simpa [step, ← List.flatMap_append] using h

theorem rounds_occurrences (n fuel l : ℕ) (ts : List Tree) :
    ((rounds n fuel l ts).flatMap Tree.leaves).Perm (ts.flatMap Tree.leaves) := by
  induction fuel generalizing l ts with
  | zero => exact List.Perm.refl _
  | succ fuel ih => exact (ih (l+1) (step n l ts)).trans (step_occurrences n l ts)

/-- Exact arithmetic at every addition gives the sum of all leaves of any tree. -/
theorem eval_zero (t : Tree) :
    t.eval (fun _ _ => 0) = (t.leaves.map Prod.snd).sum := by
  induction t with
  | leaf i x => simp [Tree.eval, Tree.leaves]
  | add l k a b ha hb => simp [Tree.eval, Tree.leaves, ha, hb]

theorem pair_height (l k h : ℕ) (as bs : List Tree)
    (ha : ∀ t ∈ as, t.height ≤ h) (hb : ∀ t ∈ bs, t.height ≤ h) :
    ∀ t ∈ pair l k as bs, t.height ≤ h + 1 := by
  induction as generalizing k bs with
  | nil => simpa [pair] using fun t ht => (hb t ht).trans (Nat.le_succ h)
  | cons a as ih =>
    cases bs with
    | nil => simpa [pair] using fun t ht => (ha t ht).trans (Nat.le_succ h)
    | cons b bs =>
      intro t ht
      simp only [pair, List.mem_cons] at ht
      rcases ht with rfl | ht
      · simp only [Tree.height]
        exact Nat.add_le_add_right (max_le (ha a (by simp)) (hb b (by simp))) 1
      · exact ih (k+1) bs (fun t ht => ha t (by simp [ht]))
          (fun t ht => hb t (by simp [ht])) t ht

theorem step_height (n l h : ℕ) (ts : List Tree)
    (ht : ∀ t ∈ ts, t.height ≤ h) :
    ∀ t ∈ step n l ts, t.height ≤ h + 1 := by
  apply pair_height
  · intro t hmem
    exact ht t (List.mem_of_mem_take hmem)
  · intro t hmem
    exact ht t (List.mem_of_mem_drop hmem)

theorem rounds_height (n fuel l h : ℕ) (ts : List Tree)
    (ht : ∀ t ∈ ts, t.height ≤ h) :
    ∀ t ∈ rounds n fuel l ts, t.height ≤ h + fuel := by
  induction fuel generalizing l h ts with
  | zero => simpa [rounds] using ht
  | succ fuel ih =>
    simpa [rounds, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (l+1) (h+1) (step n l ts) (step_height n l h ts ht)

/-- The algorithm's trees have at most ceil(log₂ n) additions on each path. -/
theorem forest_height (xs : List ℝ) :
    ∀ t ∈ forest xs, t.height ≤ depth xs.length := by
  have h0 : ∀ t ∈ (xs.zipIdx.map fun p => Tree.leaf p.2 p.1), t.height ≤ 0 := by
    intro t ht
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ht
    exact Nat.le_refl 0
  simpa [forest] using rounds_height xs.length (depth xs.length) 0 0
    (xs.zipIdx.map fun p => Tree.leaf p.2 p.1) h0

/-- Original occurrence indices and values survive every round, as a multiset. -/
theorem forest_occurrences (xs : List ℝ) :
    ((forest xs).flatMap Tree.leaves).Perm
      (xs.zipIdx.map fun p => (p.2, p.1)) := by
  have h := rounds_occurrences xs.length (depth xs.length) 0
    (xs.zipIdx.map fun p => Tree.leaf p.2 p.1)
  have he : ∀ ps : List (ℝ × ℕ),
      ps.flatMap (fun p => [(p.2, p.1)]) = ps.map (fun p => (p.2, p.1)) := by
    intro ps
    induction ps with
    | nil => rfl
    | cons p ps ih => simp [ih]
  simpa [forest, List.flatMap_map, Function.comp_def, Tree.leaves, he] using h

/-- Exact componentwise backward-error identity, before estimating the factors. -/
theorem backward_identity (t : Tree) (δ : ℕ → ℕ → ℝ) :
    t.eval δ = ((t.terms δ).map
      fun p => p.1.2 + (p.2 - 1) * p.1.2).sum := by
  rw [eval_expansion]
  congr 1
  apply List.map_congr_left
  intro p _
  ring

/-- A factor estimate yields the corresponding componentwise perturbation estimate. -/
theorem perturbation_bound (x w g : ℝ) (h : |w - 1| ≤ g) :
    |(w - 1) * x| ≤ g * |x| := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right h (abs_nonneg x)

end Bhola
