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

namespace Bhola

theorem pair_length (l k : ℕ) (as bs : List Tree) :
    (pair l k as bs).length = max as.length bs.length := by
  induction as generalizing k bs with
  | nil => simp [pair]
  | cons a as ih =>
    cases bs with
    | nil => simp [pair]
    | cons b bs => simpa [pair, ih] using
        (Nat.succ_max_succ as.length bs.length).symm

private theorem ceil_half (n l : ℕ) :
    (n ⌈/⌉ 2^l) ⌈/⌉ 2 = n ⌈/⌉ 2^(l+1) := by
  apply Nat.le_antisymm
  · apply (ceilDiv_le_iff_le_mul (by positivity : 0 < (2:ℕ))).2
    apply (ceilDiv_le_iff_le_mul (by positivity : 0 < 2^l)).2
    simpa [pow_succ, Nat.mul_assoc] using
      (le_smul_ceilDiv (b := n) (by positivity : 0 < 2^(l+1)))
  · apply (ceilDiv_le_iff_le_mul (by positivity : 0 < 2^(l+1))).2
    have h := le_smul_ceilDiv (b := n) (by positivity : 0 < 2^l)
    have h' := le_smul_ceilDiv (b := n ⌈/⌉ 2^l) (by positivity : 0 < (2:ℕ))
    simpa [pow_succ, Nat.mul_assoc] using h.trans (Nat.mul_le_mul_left (2^l) h')

theorem step_length (n l : ℕ) (ts : List Tree)
    (h : ts.length = n ⌈/⌉ 2^l) :
    (step n l ts).length = n ⌈/⌉ 2^(l+1) := by
  have hc := ceil_half n l
  have he : offset n l = (ts.length + 1) / 2 := by
    rw [offset, ← Nat.ceilDiv_eq_add_pred_div, ← hc, ← h,
      Nat.ceilDiv_eq_add_pred_div]
    omega
  rw [step, pair_length, List.length_take, List.length_drop, he]
  rw [← hc, ← h, Nat.ceilDiv_eq_add_pred_div]
  omega

theorem rounds_length (n fuel l : ℕ) (ts : List Tree)
    (h : ts.length = n ⌈/⌉ 2^l) :
    (rounds n fuel l ts).length = n ⌈/⌉ 2^(l+fuel) := by
  induction fuel generalizing l ts with
  | zero => simpa [rounds] using h
  | succ fuel ih =>
    simpa [rounds, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (l+1) (step n l ts) (step_length n l ts h)

theorem forest_length (xs : List ℝ) (hne : xs ≠ []) : (forest xs).length = 1 := by
  have h := rounds_length xs.length (depth xs.length) 0
    (xs.zipIdx.map fun p => Tree.leaf p.2 p.1) (by simp)
  have hn : 0 < xs.length := List.length_pos_iff.mpr hne
  have hp : 0 < 2 ^ depth xs.length := by positivity
  have hl : xs.length ≤ 2 ^ depth xs.length := Nat.le_pow_clog (by decide) _
  have hu : xs.length ⌈/⌉ 2 ^ depth xs.length ≤ 1 :=
    (ceilDiv_le_iff_le_mul hp).2 (by simpa using hl)
  have hz := le_smul_ceilDiv (b := xs.length) hp
  change (rounds _ _ _ _).length = 1
  rw [h]
  simp only [Nat.zero_add]
  simp only [smul_eq_mul] at hz
  by_contra hh
  have he : xs.length ⌈/⌉ 2 ^ depth xs.length = 0 := by omega
  rw [he, Nat.mul_zero] at hz
  omega

theorem forest_singleton (xs : List ℝ) (hne : xs ≠ []) :
    ∃ t, forest xs = [t] ∧ t.height ≤ depth xs.length ∧
      t.leaves.Perm (xs.zipIdx.map fun p => (p.2, p.1)) := by
  have hh := forest_length xs hne
  cases he : forest xs with
  | nil => simp [he] at hh
  | cons t ts =>
    have hts : ts = [] := by simpa [he] using hh
    have ht : forest xs = [t] := by simpa [hts] using he
    refine ⟨t, by simp [hts], forest_height xs t (by simp [ht]), ?_⟩
    simpa [ht] using forest_occurrences xs

end Bhola

namespace Bhola
private theorem gamma_step (u w e : ℝ) (d : ℕ) (hu : 0 ≤ u)
    (hd : ((d+1 : ℕ) : ℝ)*u < 1) (he : |e| ≤ u)
    (hw : |w-1| ≤ gamma u d) : |w*(1+e)-1| ≤ gamma u (d+1) := by
  have hp : 0 < 1 - (d:ℝ)*u := by push_cast at hd; nlinarith
  have hq : 0 < 1 - ((d+1:ℕ):ℝ)*u := by linarith
  have hg : 0 ≤ gamma u d := div_nonneg (by positivity) hp.le
  calc
    |w*(1+e)-1| = |(w-1)*(1+e)+e| := by congr 1; ring
    _ ≤ |w-1| * |1+e| + |e| := by simpa [abs_mul] using abs_add_le ((w-1)*(1+e)) e
    _ ≤ gamma u d * (1+u)+u := by
      have he' : |1+e| ≤ 1+u := (abs_add_le 1 e).trans (by simpa using add_le_add_left he 1)
      exact add_le_add (mul_le_mul hw he' (abs_nonneg _) hg) he
    _ ≤ gamma u (d+1) := by
      unfold gamma
      apply (le_div_iff₀ hq).2
      have hz : 0 ≤ (d:ℝ)*u^2 := by positivity
      push_cast at *
      field_simp
      nlinarith

theorem terms_bound (t : Tree) (δ : ℕ → ℕ → ℝ) (u : ℝ)
    (hv : ValidErrors u δ) (d : ℕ) (ht : t.height ≤ d)
    (hd : (d:ℝ)*u < 1) : ∀ p ∈ t.terms δ, |p.2-1| ≤ gamma u d := by
  induction t generalizing d with
  | leaf i x =>
    intro p hp
    simp only [Tree.terms, List.mem_singleton] at hp
    subst p
    simp only [sub_self, abs_zero]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hv.1) (by linarith)
  | add l k a b ia ib =>
    cases d with
    | zero => simp [Tree.height] at ht
    | succ d =>
      have hab : a.height ≤ d ∧ b.height ≤ d := by simpa [Tree.height] using ht
      have hd' : (d:ℝ)*u < 1 := by push_cast at hd; nlinarith [hv.1]
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      apply gamma_step u q.2 (δ l k) d hv.1 hd (hv.2 l k)
      rcases List.mem_append.mp hq with hq | hq
      · exact ia d hab.1 hd' q hq
      · exact ib d hab.2 hd' q hq

end Bhola

namespace Bhola
/-- Theorem 3.1. Each entry is ((original index, original value), perturbation).
The permutation clause preserves every indexed occurrence, even equal values.
The sum and bounds are for the actual returned result of Algorithm 1. -/
theorem theorem_3_1 (xs : List ℝ) (hne : xs ≠ []) (u : ℝ)
    (δ : ℕ → ℕ → ℝ) (hv : ValidErrors u δ)
    (hd : (depth xs.length : ℝ) * u < 1) :
    ∃ perturbations : List ((ℕ × ℝ) × ℝ),
      (perturbations.map Prod.fst).Perm (xs.zipIdx.map fun p => (p.2, p.1)) ∧
      algorithm xs δ = (perturbations.map fun p => p.1.2 + p.2).sum ∧
      (∀ p ∈ perturbations, |p.2| ≤ gamma u (depth xs.length) * |p.1.2|) ∧
      ∃ t, forest xs = [t] ∧ t.height ≤ depth xs.length := by
  obtain ⟨t, ht, hh, ho⟩ := forest_singleton xs hne
  refine ⟨(t.terms δ).map (fun p => (p.1, (p.2-1)*p.1.2)), ?_, ?_, ?_, t, ht, hh⟩
  · simpa only [List.map_map, Function.comp_def, terms_occurrences] using
      (terms_occurrences t δ ▸ ho)
  · simpa [algorithm, ht, List.map_map, Function.comp_def] using backward_identity t δ
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact perturbation_bound q.1.2 q.2 _ (terms_bound t δ u hv _ hh hd q hq)

/-- In exact arithmetic the algorithm sums all original input values. -/
theorem algorithm_exact (xs : List ℝ) (hne : xs ≠ []) :
    algorithm xs (fun _ _ => 0) = xs.sum := by
  obtain ⟨t, ht, _, ho⟩ := forest_singleton xs hne
  simp only [algorithm, ht]
  rw [eval_zero]
  have h := (ho.map Prod.snd).sum_eq
  simpa [List.map_map, Function.comp_def] using h

end Bhola
