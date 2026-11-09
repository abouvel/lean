import Mathlib

/-! Algorithm 1 and Theorem 3.1 of Sahil Bhola's binary-tree reduction.
The arithmetic operation is an arbitrary deterministic function satisfying the
relative-error model. Carrying a node performs no arithmetic operation. -/
namespace Bhola

inductive Tree where
  | leaf : ℝ → Tree
  | node : Tree → Tree → Tree
  deriving Inhabited

namespace Tree

def leaves : Tree → List ℝ
  | .leaf x => [x]
  | .node a b => a.leaves ++ b.leaves

def height : Tree → ℕ
  | .leaf _ => 0
  | .node a b => max a.height b.height + 1

def eval (add : ℝ → ℝ → ℝ) : Tree → ℝ
  | .leaf x => x
  | .node a b => add (a.eval add) (b.eval add)

end Tree

/-- Pair two blocks by equal offsets; excess entries are carried unchanged. -/
def pair : List Tree → List Tree → List Tree
  | [], ys => ys
  | xs, [] => xs
  | a :: xs, b :: ys => Tree.node a b :: pair xs ys

/-- One parallel stage, with zero-based offset `ceil(length / 2)`. -/
def round (xs : List Tree) : List Tree :=
  let h := (xs.length + 1) / 2
  pair (xs.take h) (xs.drop h)

def stages : ℕ → List Tree → List Tree
  | 0, xs => xs
  | k + 1, xs => stages k (round xs)

/-- The exact natural-number ceiling of the base-two logarithm. -/
def depth (n : ℕ) : ℕ := Nat.clog 2 n

/-- Symbolic expression tree for Algorithm 1. -/
def treeAlgorithm (add : ℝ → ℝ → ℝ) (xs : List ℝ) : ℝ :=
  ((stages (depth xs.length) (xs.map Tree.leaf)).headD (.leaf 0)).eval add

/-- Pair offset blocks. In particular, the unmatched branch returns `xs`
verbatim, without evaluating `add x 0`. -/
def pairValues (add : ℝ → ℝ → ℝ) : List ℝ → List ℝ → List ℝ
  | [], ys => ys
  | xs, [] => xs
  | a :: xs, b :: ys => add a b :: pairValues add xs ys

/-- Lines 4–10: simultaneous additions from the old stage's two blocks. -/
def roundValues (add : ℝ → ℝ → ℝ) (xs : List ℝ) : List ℝ :=
  let h := (xs.length + 1) / 2
  pairValues add (xs.take h) (xs.drop h)

/-- The outer loop, with exactly `k` stages. -/
def stagesValues (add : ℝ → ℝ → ℝ) : ℕ → List ℝ → List ℝ
  | 0, xs => xs
  | k + 1, xs => stagesValues add k (roundValues add xs)

/-- Algorithm 1. The default is irrelevant for the nonempty-input theorems. -/
def algorithm (add : ℝ → ℝ → ℝ) (xs : List ℝ) : ℝ :=
  (stagesValues add (depth xs.length) xs).headD 0

lemma pairValues_entry (add : ℝ → ℝ → ℝ) (xs ys : List ℝ) (k : ℕ) :
    (pairValues add xs ys)[k]? =
      match xs[k]?, ys[k]? with
      | some a, some b => some (add a b)
      | some a, none => some a
      | none, some b => some b
      | none, none => none := by
  induction xs generalizing ys k with
  | nil =>
    cases h : ys[k]? <;> simp [pairValues, h]
  | cons a xs ih =>
    cases ys with
    | nil => cases h : (a :: xs)[k]? <;> simp [pairValues, h]
    | cons b ys =>
      cases k with
      | zero => simp [pairValues]
      | succ k => simpa only [pairValues, List.getElem?_cons_succ] using ih ys k

/-- Lines 5–9, with zero-based indices: pair at the ceiling-half offset
when that entry exists, and otherwise return the original entry unchanged. -/
theorem roundValues_entry (add : ℝ → ℝ → ℝ) (xs : List ℝ) (k : ℕ)
    (hk : k < (xs.length + 1) / 2) :
    (roundValues add xs)[k]? =
      if hj : k + (xs.length + 1) / 2 < xs.length then
        some (add (xs[k]'(by omega)) (xs[k + (xs.length + 1) / 2]'hj))
      else some (xs[k]'(by omega)) := by
  have hk' : k < xs.length := by omega
  simp only [roundValues, pairValues_entry, List.getElem?_take, List.getElem?_drop]
  rw [if_pos hk, List.getElem?_eq_getElem hk']
  by_cases hj : k + (xs.length + 1) / 2 < xs.length
  · rw [List.getElem?_eq_getElem (by omega : (xs.length + 1) / 2 + k < xs.length)]
    simp [hj, Nat.add_comm]
  · rw [List.getElem?_eq_none (by omega : xs.length ≤ (xs.length + 1) / 2 + k)]
    simp [hj]

lemma pair_eval (add : ℝ → ℝ → ℝ) (xs ys : List Tree) :
    (pair xs ys).map (Tree.eval add) =
      pairValues add (xs.map (Tree.eval add)) (ys.map (Tree.eval add)) := by
  induction xs generalizing ys with
  | nil => simp [pair, pairValues]
  | cons a xs ih =>
    cases ys with
    | nil => simp [pair, pairValues]
    | cons b ys => simp [pair, pairValues, Tree.eval, ih]

lemma round_eval (add : ℝ → ℝ → ℝ) (xs : List Tree) :
    (round xs).map (Tree.eval add) = roundValues add (xs.map (Tree.eval add)) := by
  simp [round, roundValues, pair_eval, List.map_take, List.map_drop]

lemma stages_eval (add : ℝ → ℝ → ℝ) (k : ℕ) (xs : List Tree) :
    (stages k xs).map (Tree.eval add) = stagesValues add k (xs.map (Tree.eval add)) := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih => rw [stages, ih, round_eval, stagesValues]

lemma pair_length (xs ys : List Tree) :
    (pair xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [pair]
  | cons a xs ih =>
    cases ys with
    | nil => simp [pair]
    | cons b ys => simp [pair, ih, max_add_add_right]

lemma round_length (xs : List Tree) :
    (round xs).length = (xs.length + 1) / 2 := by
  rw [round, pair_length, List.length_take, List.length_drop]
  have h : (xs.length + 1) / 2 ≤ xs.length := by omega
  rw [min_eq_left h, max_eq_left]
  omega

lemma pair_leaves (xs ys : List Tree) :
    ((pair xs ys).flatMap Tree.leaves).Perm
      (xs.flatMap Tree.leaves ++ ys.flatMap Tree.leaves) := by
  induction xs generalizing ys with
  | nil => simp [pair]
  | cons a xs ih =>
    cases ys with
    | nil => simp [pair]
    | cons b ys =>
      simp only [pair, List.flatMap_cons, Tree.leaves]
      have h := (ih ys).append_left (a.leaves ++ b.leaves)
      simp only [List.append_assoc] at h ⊢
      apply h.trans
      simpa only [List.append_assoc] using
        ((List.perm_append_comm (l₁ := b.leaves) (l₂ := xs.flatMap Tree.leaves)).append_right
          (ys.flatMap Tree.leaves)).append_left a.leaves

lemma round_leaves (xs : List Tree) :
    ((round xs).flatMap Tree.leaves).Perm (xs.flatMap Tree.leaves) := by
  have h := pair_leaves (xs.take ((xs.length + 1) / 2))
    (xs.drop ((xs.length + 1) / 2))
  simpa [round, ← List.flatMap_append] using h

lemma stages_leaves (k : ℕ) (xs : List Tree) :
    ((stages k xs).flatMap Tree.leaves).Perm (xs.flatMap Tree.leaves) := by
  induction k generalizing xs with
  | zero => exact List.Perm.refl _
  | succ k ih => exact (ih (round xs)).trans (round_leaves xs)

lemma pair_height (xs ys : List Tree) (d : ℕ)
    (hx : ∀ t ∈ xs, t.height ≤ d) (hy : ∀ t ∈ ys, t.height ≤ d) :
    ∀ t ∈ pair xs ys, t.height ≤ d + 1 := by
  induction xs generalizing ys with
  | nil => simpa [pair] using fun t ht => (hy t ht).trans (Nat.le_succ d)
  | cons a xs ih =>
    cases ys with
    | nil => simpa [pair] using fun t ht => (hx t ht).trans (Nat.le_succ d)
    | cons b ys =>
      intro t ht
      simp only [pair, List.mem_cons] at ht
      rcases ht with rfl | ht
      · simp only [Tree.height, Nat.add_le_add_iff_right, max_le_iff]
        exact ⟨hx a (by simp), hy b (by simp)⟩
      · exact ih ys (fun t ht => hx t (by simp [ht]))
          (fun t ht => hy t (by simp [ht])) t ht

lemma round_height (xs : List Tree) (d : ℕ)
    (hx : ∀ t ∈ xs, t.height ≤ d) :
    ∀ t ∈ round xs, t.height ≤ d + 1 := by
  apply pair_height
  · intro t ht; exact hx t (List.mem_of_mem_take ht)
  · intro t ht; exact hx t (List.mem_of_mem_drop ht)

lemma stages_height (k d : ℕ) (xs : List Tree)
    (hx : ∀ t ∈ xs, t.height ≤ d) :
    ∀ t ∈ stages k xs, t.height ≤ d + k := by
  induction k generalizing d xs with
  | zero => simpa [stages] using hx
  | succ k ih =>
    simpa [stages, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (d + 1) (round xs) (round_height xs d hx)

lemma half_pos {n : ℕ} (hn : 0 < n) : 0 < (n + 1) / 2 := by omega

lemma stages_length (k : ℕ) (xs : List Tree) (hn : 0 < xs.length) :
    (stages k xs).length = (xs.length - 1) / 2 ^ k + 1 := by
  induction k generalizing xs with
  | zero => simp [stages]; omega
  | succ k ih =>
    rw [stages, ih (round xs) (by rw [round_length]; exact half_pos hn), round_length]
    have h : (xs.length + 1) / 2 - 1 = (xs.length - 1) / 2 := by omega
    rw [h, Nat.div_div_eq_div_mul, pow_succ]
    congr 2
    omega

/-- Stage sizes and therefore the pairing offsets agree with the paper's
`ceil(n / 2^ℓ)` formula, even when the input size is not a power of two. -/
lemma stages_length_ceiling (k : ℕ) (xs : List Tree) (hn : 0 < xs.length) :
    (stages k xs).length = (xs.length + 2 ^ k - 1) / 2 ^ k := by
  rw [stages_length k xs hn]
  have hp : 0 < 2 ^ k := pow_pos (by decide) _
  have h : xs.length + 2 ^ k - 1 = (xs.length - 1) + 2 ^ k := by omega
  rw [h, Nat.add_div_right _ hp]

lemma final_tree (xs : List ℝ) (hn : xs ≠ []) :
    ∃ t, stages (depth xs.length) (xs.map Tree.leaf) = [t] ∧
      t.leaves.Perm xs ∧ t.height ≤ depth xs.length := by
  have hn' : 0 < xs.length := List.length_pos_iff.mpr hn
  have hp : xs.length ≤ 2 ^ depth xs.length :=
    (Nat.clog_le_iff_le_pow (by decide)).mp (le_refl _)
  have hl : (stages (depth xs.length) (xs.map Tree.leaf)).length = 1 := by
    rw [stages_length _ _ (by simpa using hn'), List.length_map]
    rw [Nat.div_eq_of_lt (by omega : xs.length - 1 < 2 ^ depth xs.length)]
  obtain ⟨t, ht⟩ := List.length_eq_one_iff.mp hl
  refine ⟨t, ht, ?_, ?_⟩
  · have h := stages_leaves (depth xs.length) (xs.map Tree.leaf)
    simpa [ht, List.flatMap_map, Tree.leaves, List.flatMap_singleton] using h
  · have h := stages_height (depth xs.length) 0 (xs.map Tree.leaf)
      (by intro t ht; obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht; simp [Tree.height])
    simpa [ht] using h t (by simp [ht])

/-- The numerical loop and its symbolic expression tree compute the same value. -/
lemma algorithm_eq_tree (add : ℝ → ℝ → ℝ) (xs : List ℝ) (hn : xs ≠ []) :
    algorithm add xs = treeAlgorithm add xs := by
  obtain ⟨t, ht, _, _⟩ := final_tree xs hn
  have h := stages_eval add (depth xs.length) (xs.map Tree.leaf)
  simp only [ht, List.map_cons, List.map_nil, List.map_map] at h
  have hv : stagesValues add (depth xs.length) xs = [t.eval add] := by
    simpa [Function.comp_def, Tree.eval] using h.symm
  simp [algorithm, treeAlgorithm, ht, hv]

/-- The standard deterministic error constant, used only when `d*u < 1`. -/
noncomputable def gamma (d : ℕ) (u : ℝ) : ℝ := (d : ℝ) * u / (1 - (d : ℝ) * u)

lemma gamma_nonneg {d : ℕ} {u : ℝ} (hu : 0 ≤ u) (hd : (d : ℝ) * u < 1) :
    0 ≤ gamma d u := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

lemma gamma_step {d : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (hd : ((d + 1 : ℕ) : ℝ) * u < 1) :
    gamma d u * (1 + u) + u ≤ gamma (d + 1) u := by
  have hd' : (d : ℝ) * u < 1 := by push_cast at hd; nlinarith
  have h₀ : 0 < 1 - (d : ℝ) * u := by linarith
  have h₁ : 0 < 1 - ((d + 1 : ℕ) : ℝ) * u := by linarith
  calc
    gamma d u * (1 + u) + u =
        (((d + 1 : ℕ) : ℝ) * u) / (1 - (d : ℝ) * u) := by
      dsimp [gamma]
      push_cast
      field_simp
      ring
    _ ≤ gamma (d + 1) u := by
      apply div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hu) h₁
      push_cast
      nlinarith

/-- No overflow or underflow: every executed addition obeys (1). -/
def RoundingModel (add : ℝ → ℝ → ℝ) (u : ℝ) : Prop :=
  ∀ a b, ∃ δ : ℝ, |δ| ≤ u ∧ add a b = (a + b) * (1 + δ)

/-- The relative-error assumption only at additions actually present in a tree.
Leaves and carried nodes introduce no rounding error. -/
def Tree.Valid (add : ℝ → ℝ → ℝ) (u : ℝ) : Tree → Prop
  | .leaf _ => True
  | .node a b => a.Valid add u ∧ b.Valid add u ∧
      ∃ δ : ℝ, |δ| ≤ u ∧
        add (a.eval add) (b.eval add) = (a.eval add + b.eval add) * (1 + δ)

/-- No overflow/underflow and the standard model for this particular run.
The final expression tree contains the actual executed additions. -/
def ExecutionModel (add : ℝ → ℝ → ℝ) (u : ℝ) (xs : List ℝ) : Prop :=
  ∀ t ∈ stages (depth xs.length) (xs.map Tree.leaf), t.Valid add u

lemma valid_of_roundingModel (add : ℝ → ℝ → ℝ) {u : ℝ}
    (hm : RoundingModel add u) (t : Tree) : t.Valid add u := by
  induction t with
  | leaf _ => trivial
  | node a b ha hb => exact ⟨ha, hb, hm _ _⟩

lemma executionModel_of_roundingModel (add : ℝ → ℝ → ℝ) {u : ℝ}
    (hm : RoundingModel add u) (xs : List ℝ) : ExecutionModel add u xs := by
  intro t _
  exact valid_of_roundingModel add hm t

lemma scale_error {d : ℕ} {u x z δ : ℝ} (hu : 0 ≤ u)
    (hd : ((d + 1 : ℕ) : ℝ) * u < 1)
    (hz : |z - x| ≤ gamma d u * |x|) (he : |δ| ≤ u) :
    |z * (1 + δ) - x| ≤ gamma (d + 1) u * |x| := by
  have hd' : (d : ℝ) * u < 1 := by push_cast at hd; nlinarith
  have hg := gamma_nonneg hu hd'
  have hf : |1 + δ| ≤ 1 + u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + u := by simpa using add_le_add_left he 1
  calc
    |z * (1 + δ) - x| = |(z - x) * (1 + δ) + x * δ| := by congr 1; ring
    _ ≤ |z - x| * |1 + δ| + |x| * |δ| := by
      simpa only [abs_mul] using abs_add_le ((z - x) * (1 + δ)) (x * δ)
    _ ≤ (gamma d u * |x|) * (1 + u) + |x| * u :=
      add_le_add (mul_le_mul hz hf (abs_nonneg _) (mul_nonneg hg (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left he (abs_nonneg _))
    _ = (gamma d u * (1 + u) + u) * |x| := by ring
    _ ≤ gamma (d + 1) u * |x| :=
      mul_le_mul_of_nonneg_right (gamma_step hu hd) (abs_nonneg _)

lemma forall₂_scale {xs zs : List ℝ} {d : ℕ} {u δ : ℝ}
    (hu : 0 ≤ u) (hd : ((d + 1 : ℕ) : ℝ) * u < 1) (he : |δ| ≤ u)
    (h : List.Forall₂ (fun x z => |z - x| ≤ gamma d u * |x|) xs zs) :
    List.Forall₂ (fun x z => |z - x| ≤ gamma (d + 1) u * |x|)
      xs (zs.map (fun z => z * (1 + δ))) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (scale_error hu hd h he) ih

lemma forall₂_append {α β : Type*} {R : α → β → Prop}
    {a b : List α} {c d : List β} (h : List.Forall₂ R a c)
    (h' : List.Forall₂ R b d) : List.Forall₂ R (a ++ b) (c ++ d) := by
  induction h with
  | nil => exact h'
  | cons he _ ih => exact .cons he ih

/-- A separate perturbation for every leaf occurrence. -/
lemma tree_backward_error_local (add : ℝ → ℝ → ℝ) {u : ℝ}
    (hu : 0 ≤ u) (d : ℕ)
    (hd : (d : ℝ) * u < 1) (t : Tree) (ht : t.height ≤ d)
    (hm : t.Valid add u) :
    ∃ zs : List ℝ,
      List.Forall₂ (fun x z => |z - x| ≤ gamma d u * |x|) t.leaves zs ∧
      t.eval add = zs.sum := by
  induction d generalizing t with
  | zero =>
    cases t with
    | leaf x => exact ⟨[x], .cons (by simp [gamma]) .nil, by simp [Tree.eval]⟩
    | node a b => simp [Tree.height] at ht
  | succ d ih =>
    cases t with
    | leaf x =>
      refine ⟨[x], .cons ?_ .nil, by simp [Tree.eval]⟩
      simpa using mul_nonneg (gamma_nonneg hu hd) (abs_nonneg x)
    | node a b =>
      have hd' : (d : ℝ) * u < 1 := by push_cast at hd; nlinarith
      have hab : a.height ≤ d ∧ b.height ≤ d := by
        simpa [Tree.height, max_le_iff] using ht
      obtain ⟨za, ha, ea⟩ := ih hd' a hab.1 hm.1
      obtain ⟨zb, hb, eb⟩ := ih hd' b hab.2 hm.2.1
      obtain ⟨δ, he, ee⟩ := hm.2.2
      refine ⟨(za ++ zb).map (fun z => z * (1 + δ)), ?_, ?_⟩
      · exact forall₂_scale hu hd he (forall₂_append ha hb)
      · change add (a.eval add) (b.eval add) = _
        rw [ee, ea, eb, List.sum_map_mul_right]
        simp

/-- Theorem 3.1, in an occurrence-preserving list formulation.
`zs` lists the perturbed inputs in the original input order. -/
theorem theorem_3_1_list_local (add : ℝ → ℝ → ℝ) (xs : List ℝ)
    (hn : xs ≠ []) {u : ℝ} (hu : 0 ≤ u) (hm : ExecutionModel add u xs)
    (hd : (depth xs.length : ℝ) * u < 1) :
    ∃ zs : List ℝ,
      List.Forall₂ (fun x z => |z - x| ≤ gamma (depth xs.length) u * |x|) xs zs ∧
      algorithm add xs = zs.sum := by
  obtain ⟨t, ht, hp, hh⟩ := final_tree xs hn
  obtain ⟨zs, hz, he⟩ := tree_backward_error_local add hu _ hd t hh (hm t (by simp [ht]))
  obtain ⟨ws, hw, hperm⟩ := List.perm_comp_forall₂ hp.symm hz
  refine ⟨ws, hw, ?_⟩
  rw [algorithm_eq_tree add xs hn]
  simpa [treeAlgorithm, ht, he] using hperm.sum_eq.symm

/-- Theorem 3.1 with perturbations indexed by the original occurrences. -/
theorem theorem_3_1 (add : ℝ → ℝ → ℝ) (xs : List ℝ)
    (hn : xs ≠ []) {u : ℝ} (hu : 0 ≤ u) (hm : ExecutionModel add u xs)
    (hd : (depth xs.length : ℝ) * u < 1) :
    ∃ Δ : Fin xs.length → ℝ,
      algorithm add xs = ∑ i : Fin xs.length, (xs.get i + Δ i) ∧
      ∀ i, |Δ i| ≤ gamma (depth xs.length) u * |xs.get i| := by
  obtain ⟨zs, hz, he⟩ := theorem_3_1_list_local add xs hn hu hm hd
  let z : Fin xs.length → ℝ := fun i => zs.get (Fin.cast hz.length_eq i)
  have hlist : List.ofFn z = zs := by
    apply List.ext_get
    · simp [hz.length_eq]
    · intro i hi hj
      simp [z]
  refine ⟨fun i => z i - xs.get i, ?_, ?_⟩
  · simp only [add_sub_cancel]
    rw [he, ← hlist, List.sum_ofFn]
  · intro i
    exact hz.get i.isLt (by simpa [hz.length_eq] using i.isLt)

/-- Convenient corollary for a total operation satisfying the standard model. -/
theorem theorem_3_1_global (add : ℝ → ℝ → ℝ) (xs : List ℝ)
    (hn : xs ≠ []) {u : ℝ} (hu : 0 ≤ u) (hm : RoundingModel add u)
    (hd : (depth xs.length : ℝ) * u < 1) :
    ∃ Δ : Fin xs.length → ℝ,
      algorithm add xs = ∑ i : Fin xs.length, (xs.get i + Δ i) ∧
      ∀ i, |Δ i| ≤ gamma (depth xs.length) u * |xs.get i| :=
  theorem_3_1 add xs hn hu (executionModel_of_roundingModel add hm xs) hd

lemma Tree.leaves_length_le (t : Tree) : t.leaves.length ≤ 2 ^ t.height := by
  induction t with
  | leaf x => simp [Tree.leaves, Tree.height]
  | node a b ha hb =>
    have h₁ : 2 ^ a.height ≤ 2 ^ max a.height b.height :=
      Nat.pow_le_pow_right (by decide) (le_max_left _ _)
    have h₂ : 2 ^ b.height ≤ 2 ^ max a.height b.height :=
      Nat.pow_le_pow_right (by decide) (le_max_right _ _)
    simp only [Tree.leaves, List.length_append, Tree.height, pow_succ]
    omega

/-- The final tree has exactly the stated logarithmic depth. -/
theorem algorithm_tree_spec (xs : List ℝ) (hn : xs ≠ []) :
    ∃ t, stages (depth xs.length) (xs.map Tree.leaf) = [t] ∧
      t.leaves.Perm xs ∧ t.height = depth xs.length := by
  obtain ⟨t, ht, hp, hh⟩ := final_tree xs hn
  refine ⟨t, ht, hp, Nat.le_antisymm hh ?_⟩
  apply Nat.clog_le_of_le_pow
  rw [← hp.length_eq]
  exact t.leaves_length_le

lemma stages_succ (k : ℕ) (xs : List Tree) :
    stages (k + 1) xs = round (stages k xs) := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih => exact ih (round xs)

/-- The offset at stage `ℓ` is precisely `ceil(n / 2^(ℓ+1))`. -/
theorem stage_offset (xs : List Tree) (hn : 0 < xs.length) (ℓ : ℕ) :
    ((stages ℓ xs).length + 1) / 2 =
      (xs.length + 2 ^ (ℓ + 1) - 1) / 2 ^ (ℓ + 1) := by
  rw [← round_length, ← stages_succ, stages_length_ceiling _ _ hn]

/-- The numerical implementation has the paper's stage sizes, for every stage. -/
theorem stagesValues_length (add : ℝ → ℝ → ℝ) (xs : List ℝ)
    (hn : xs ≠ []) (ℓ : ℕ) :
    (stagesValues add ℓ xs).length = (xs.length + 2 ^ ℓ - 1) / 2 ^ ℓ := by
  have h := stages_eval add ℓ (xs.map Tree.leaf)
  have he : (stages ℓ (xs.map Tree.leaf)).map (Tree.eval add) =
      stagesValues add ℓ xs := by
    simpa [List.map_map, Function.comp_def, Tree.eval] using h
  rw [← he, List.length_map, stages_length_ceiling]
  · simp
  · simpa using List.length_pos_iff.mpr hn

/-- The direct numerical loop returns the root of the certified tree. -/
theorem algorithm1_spec (add : ℝ → ℝ → ℝ) (xs : List ℝ) (hn : xs ≠ []) :
    ∃ t : Tree, stagesValues add (depth xs.length) xs = [t.eval add] ∧
      t.leaves.Perm xs ∧ t.height = depth xs.length ∧ algorithm add xs = t.eval add := by
  obtain ⟨t, ht, hp, hh⟩ := algorithm_tree_spec xs hn
  have h := stages_eval add (depth xs.length) (xs.map Tree.leaf)
  have hv : stagesValues add (depth xs.length) xs = [t.eval add] := by
    simpa [ht, List.map_map, Function.comp_def, Tree.eval] using h.symm
  exact ⟨t, hv, hp, hh, by simp [algorithm, hv]⟩

/-- Logarithmic depth is the least integer bounding the input size by a power of two. -/
theorem depth_spec (n k : ℕ) : depth n ≤ k ↔ n ≤ 2 ^ k :=
  Nat.clog_le_iff_le_pow (by decide)

/-- In exact arithmetic the same schedule sums every input occurrence. -/
theorem algorithm_exact (xs : List ℝ) (hn : xs ≠ []) :
    algorithm (· + ·) xs = xs.sum := by
  obtain ⟨t, ht, hp, _⟩ := final_tree xs hn
  have h : ∀ t : Tree, t.eval (· + ·) = t.leaves.sum := by
    intro t
    induction t with
    | leaf x => simp [Tree.eval, Tree.leaves]
    | node a b ha hb => simp [Tree.eval, Tree.leaves, ha, hb]
  rw [algorithm_eq_tree _ xs hn]
  simpa [treeAlgorithm, ht, h] using hp.sum_eq

end Bhola
