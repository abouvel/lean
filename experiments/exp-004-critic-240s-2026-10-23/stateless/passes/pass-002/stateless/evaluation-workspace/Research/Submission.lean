import Mathlib

/-! Algorithm 1 and the deterministic error model of Bhola, §3.
The rounding errors are explicit real parameters; the absence of exceptional
floating-point results is represented by the relative-error model. -/
noncomputable section

namespace Bhola

inductive Tree where
  | leaf : ℝ → Tree
  | add : Tree → Tree → ℝ → Tree
  deriving Inhabited

namespace Tree

def leaves : Tree → List ℝ
  | .leaf x => [x]
  | .add a b _ => leaves a ++ leaves b

def eval : Tree → ℝ
  | .leaf x => x
  | .add a b d => (eval a + eval b) * (1 + d)

def depth : Tree → ℕ
  | .leaf _ => 0
  | .add a b _ => max (depth a) (depth b) + 1

def Valid (u : ℝ) : Tree → Prop
  | .leaf _ => True
  | .add a b d => Valid u a ∧ Valid u b ∧ |d| ≤ u

/-- One pair per input occurrence, even if several inputs have equal values. -/
def terms : Tree → List (ℝ × ℝ)
  | .leaf x => [(x, 1)]
  | .add a b d => (terms a ++ terms b).map (fun p => (p.1, p.2 * (1 + d)))

@[simp] theorem terms_inputs (t : Tree) : (terms t).map Prod.fst = leaves t := by
  induction t with
  | leaf x => simp [terms, leaves]
  | add a b d ha hb => simpa [terms, leaves, List.map_map, Function.comp_def] using congrArg₂ List.append ha hb

theorem eval_terms (t : Tree) :
    t.eval = ((terms t).map (fun p => p.1 * p.2)).sum := by
  induction t with
  | leaf x => simp [eval, terms]
  | add a b d ha hb =>
    simp only [eval, terms, List.map_append, List.map_map, List.sum_append]
    rw [ha, hb, add_mul]
    simp only [Function.comp_def, ← mul_assoc]
    simp [← List.sum_map_mul_right]

end Tree

/-- A simultaneous level, with zero-based indices. The offset is the
ceiling half-width. The unavailable-partner branch returns the old tree. -/
def level (err : ℕ → ℝ) (ts : List Tree) : List Tree :=
  let m := (ts.length + 1) / 2
  ((ts.take m).zipIdx).map fun (a, k) =>
    match ts[k + m]? with
    | some b => .add a b (err k)
    | none => a

/-- Execute exactly the paper's ceiling-logarithm number of levels. -/
def rounds (err : ℕ → ℕ → ℝ) : ℕ → List Tree → List Tree
  | 0, ts => ts
  | k + 1, ts => level (err k) (rounds err k ts)

def algorithm (xs : List ℝ) (err : ℕ → ℕ → ℝ) : Option Tree :=
  (rounds err (Nat.clog 2 xs.length) (xs.map Tree.leaf)).head?

def gamma (k : ℕ) (u : ℝ) : ℝ := (k : ℝ) * u / (1 - (k : ℝ) * u)

/-- `Nat.clog` is exactly the ceiling of the real base-two logarithm. -/
theorem logarithmic_depth (n : ℕ) : Nat.clog 2 n = ⌈Real.logb 2 n⌉₊ := by
  simpa using (Real.natCeil_logb_natCast 2 n).symm

/-- A single relative error extends a coefficient's gamma bound. -/
theorem gamma_step {k : ℕ} {u w d : ℝ} (hu : 0 ≤ u)
    (hk : ((k + 1 : ℕ) : ℝ) * u < 1)
    (hw : |w - 1| ≤ gamma k u) (hd : |d| ≤ u) :
    |w * (1 + d) - 1| ≤ gamma (k + 1) u := by
  have hku : (k : ℝ) * u < 1 := by push_cast at hk; nlinarith
  have hden : 0 < 1 - (k : ℝ) * u := by linarith
  have hden' : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by linarith
  have hg : 0 ≤ gamma k u := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) hden.le
  have hw' : |w| ≤ 1 + gamma k u := by
    calc
      |w| = |(w - 1) + 1| := by congr 1; ring
      _ ≤ |w - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ 1 + gamma k u := by rw [abs_one]; linarith
  calc
    |w * (1 + d) - 1| = |(w - 1) + w * d| := by congr 1; ring
    _ ≤ |w - 1| + |w| * |d| := by simpa [abs_mul] using abs_add_le (w - 1) (w * d)
    _ ≤ gamma k u + (1 + gamma k u) * u := by gcongr
    _ ≤ gamma (k + 1) u := by
      unfold gamma
      apply (le_div_iff₀ hden').2
      field_simp
      push_cast at *
      nlinarith [sq_nonneg u, mul_nonneg (Nat.cast_nonneg k) (sq_nonneg u)]

/-- Every coefficient has at most `k` relative-error factors. -/
theorem coefficient_bound (k : ℕ) (t : Tree) (u : ℝ)
    (hu : 0 ≤ u) (hk : (k : ℝ) * u < 1)
    (ht : t.depth ≤ k) (hv : t.Valid u) :
    ∀ p ∈ t.terms, |p.2 - 1| ≤ gamma k u := by
  induction k generalizing t with
  | zero =>
    cases t with
    | leaf x => simp [Tree.terms, gamma]
    | add a b d => simp [Tree.depth] at ht
  | succ k ih =>
    have hk' : (k : ℝ) * u < 1 := by push_cast at hk; nlinarith
    cases t with
    | leaf x =>
      simp only [Tree.terms, List.mem_singleton]
      intro p hp
      subst p
      simp only [sub_self, abs_zero]
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith : 0 ≤ 1 - ((k+1 : ℕ) : ℝ) * u)
    | add a b d =>
      rcases hv with ⟨ha, hb, hd⟩
      have hdepth : a.depth ≤ k ∧ b.depth ≤ k := by simpa [Tree.depth, max_le_iff] using ht
      intro p hp
      simp only [Tree.terms, List.mem_map, List.mem_append] at hp
      rcases hp with ⟨q, hq, rfl⟩
      apply gamma_step hu hk _ hd
      rcases hq with hq | hq
      · exact ih a hk' hdepth.1 ha q hq
      · exact ih b hk' hdepth.2 hb q hq

/-- Componentwise backward error, preserving occurrences in a list.
Each pair consists of an original input and its individual perturbation. -/
theorem backward_error (t : Tree) (u : ℝ) (hu : 0 ≤ u)
    (hk : (t.depth : ℝ) * u < 1) (hv : t.Valid u) :
    ∃ ps : List (ℝ × ℝ),
      ps.map Prod.fst = t.leaves ∧
      t.eval = (ps.map (fun p => p.1 + p.2)).sum ∧
      ∀ p ∈ ps, |p.2| ≤ gamma t.depth u * |p.1| := by
  refine ⟨t.terms.map (fun p => (p.1, p.1 * (p.2 - 1))), ?_, ?_, ?_⟩
  · simpa [List.map_map, Function.comp_def] using t.terms_inputs
  · rw [t.eval_terms, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p hp
    dsimp
    ring
  · intro p hp
    simp only [List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩
    dsimp
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (coefficient_bound t.depth t u hu hk le_rfl hv q hq) (abs_nonneg _)

/-- A level preserves any hereditary property closed under rounded addition. -/
theorem level_property (P : Tree → Prop) (ts : List Tree) (err : ℕ → ℝ)
    (h : ∀ t ∈ ts, P t)
    (hadd : ∀ a b k, P a → P b → P (.add a b (err k))) :
    ∀ t ∈ level err ts, P t := by
  intro t ht
  simp only [level, List.mem_map] at ht
  rcases ht with ⟨⟨a, k⟩, ha, rfl⟩
  have hamem : a ∈ ts := by
    have hz := List.mem_zipIdx ha
    apply List.mem_of_mem_take
    exact List.mem_of_getElem hz.2.2.symm
  split
  next b hb => exact hadd a b k (h a hamem) (h b (List.mem_of_getElem? hb))
  next hb => exact h a hamem

 theorem level_length (ts : List Tree) (err : ℕ → ℝ) :
    (level err ts).length = (ts.length + 1) / 2 := by
  simp only [level, List.length_map, List.length_zipIdx, List.length_take]
  apply min_eq_left
  omega

/-- No path acquires more than one addition per executed level. -/
theorem rounds_depth (err : ℕ → ℕ → ℝ) (k : ℕ) (xs : List ℝ) :
    ∀ t ∈ rounds err k (xs.map Tree.leaf), t.depth ≤ k := by
  induction k with
  | zero =>
    intro t ht
    simp only [rounds, List.mem_map] at ht
    rcases ht with ⟨x, hx, rfl⟩
    simp [Tree.depth]
  | succ k ih =>
    intro t ht
    change t ∈ level (err k) (rounds err k (xs.map Tree.leaf)) at ht
    -- Use the sharper previous-level bound on both available partners.
    simp only [level, List.mem_map] at ht
    rcases ht with ⟨⟨a, j⟩, ha, rfl⟩
    have hamem : a ∈ rounds err k (xs.map Tree.leaf) := by
      have hz := List.mem_zipIdx ha
      exact List.mem_of_mem_take (List.mem_of_getElem hz.2.2.symm)
    split
    next b hb =>
      have hbmem := List.mem_of_getElem? hb
      simp only [Tree.depth, Nat.add_le_add_iff_right, max_le_iff]
      exact ⟨ih a hamem, ih b hbmem⟩
    next => exact Nat.le_succ_of_le (ih a hamem)

theorem rounds_valid (err : ℕ → ℕ → ℝ) (u : ℝ)
    (he : ∀ l j, |err l j| ≤ u) (k : ℕ) (xs : List ℝ) :
    ∀ t ∈ rounds err k (xs.map Tree.leaf), t.Valid u := by
  induction k with
  | zero =>
    intro t ht
    simp only [rounds, List.mem_map] at ht
    rcases ht with ⟨x, hx, rfl⟩
    trivial
  | succ k ih =>
    exact level_property _ _ _ ih (fun a b j ha hb => ⟨ha, hb, he k j⟩)

/-- Exact round width, expressed by its ceiling-division universal property. -/
theorem rounds_width (err : ℕ → ℕ → ℝ) (k : ℕ) (ts : List Tree) (m : ℕ) :
    (rounds err k ts).length ≤ m ↔ ts.length ≤ 2 ^ k * m := by
  induction k generalizing m with
  | zero => simp [rounds]
  | succ k ih =>
    rw [rounds, level_length]
    have half : ((rounds err k ts).length + 1) / 2 ≤ m ↔
        (rounds err k ts).length ≤ 2 * m := by omega
    rw [half, ih, pow_succ]
    ring_nf

/-- The paper's width `ceil(n / 2^k)`, as natural ceiling division. -/
theorem rounds_width_exact (err : ℕ → ℕ → ℝ) (k : ℕ) (ts : List Tree) :
    (rounds err k ts).length = ts.length ⌈/⌉ (2 ^ k) := by
  have hp : 0 < 2 ^ k := pow_pos (by decide) _
  have hw (m : ℕ) : (rounds err k ts).length ≤ m ↔
      ts.length ⌈/⌉ (2 ^ k) ≤ m := by
    rw [rounds_width, ceilDiv_le_iff_le_mul hp]
  exact le_antisymm ((hw _).mpr le_rfl) ((hw _).mp le_rfl)

/-- The implemented offset is precisely the original input width divided
by `2^(k+1)`, rounded upward; it is not adjacent pairing. -/
theorem algorithm_offset (err : ℕ → ℕ → ℝ) (k : ℕ) (xs : List ℝ) :
    ((rounds err k (xs.map Tree.leaf)).length + 1) / 2 =
      xs.length ⌈/⌉ (2 ^ (k + 1)) := by
  rw [← level_length (rounds err k (xs.map Tree.leaf)) (err k)]
  change (rounds err (k + 1) (xs.map Tree.leaf)).length = _
  simpa using rounds_width_exact err (k + 1) (xs.map Tree.leaf)

/-- No round discards the entire nonempty forest. -/
theorem rounds_nonempty (err : ℕ → ℕ → ℝ) (k : ℕ) (ts : List Tree)
    (h : ts ≠ []) : rounds err k ts ≠ [] := by
  intro hz
  have hw := (rounds_width err k ts 0).mp (by simp [hz])
  simp only [Nat.mul_zero, Nat.le_zero, List.length_eq_zero_iff] at hw
  exact h hw

/-- Algorithm 1 terminates with exactly one tree for every nonempty input. -/
theorem algorithm_singleton (xs : List ℝ) (err : ℕ → ℕ → ℝ) (hx : xs ≠ []) :
    ∃ t, rounds err (Nat.clog 2 xs.length) (xs.map Tree.leaf) = [t] ∧
      algorithm xs err = some t ∧ t.depth ≤ Nat.clog 2 xs.length := by
  have hlen : (rounds err (Nat.clog 2 xs.length) (xs.map Tree.leaf)).length ≤ 1 := by
    apply (rounds_width _ _ _ _).mpr
    simpa using Nat.le_pow_clog (by decide : 1 < 2) xs.length
  have hne := rounds_nonempty err (Nat.clog 2 xs.length) (xs.map Tree.leaf) (by simpa using hx)
  cases hs : rounds err (Nat.clog 2 xs.length) (xs.map Tree.leaf) with
  | nil => exact False.elim (hne hs)
  | cons t rest =>
    have hr : rest = [] := by simpa [hs] using hlen
    subst rest
    refine ⟨t, rfl, ?_, ?_⟩
    · simp [algorithm, hs]
    · exact rounds_depth err _ xs t (by simp [hs])

/-- Ceiling-log coefficient bound for the actual returned tree. -/
theorem algorithm_coefficients (xs : List ℝ) (err : ℕ → ℕ → ℝ)
    (hx : xs ≠ []) (u : ℝ) (hu : 0 ≤ u)
    (he : ∀ l j, |err l j| ≤ u)
    (hk : (Nat.clog 2 xs.length : ℝ) * u < 1) :
    ∃ t, algorithm xs err = some t ∧
      t.depth ≤ Nat.clog 2 xs.length ∧
      ∀ p ∈ t.terms, |p.2 - 1| ≤ gamma (Nat.clog 2 xs.length) u := by
  obtain ⟨t, hs, ha, hd⟩ := algorithm_singleton xs err hx
  refine ⟨t, ha, hd, coefficient_bound _ t u hu hk hd ?_⟩
  exact rounds_valid err u he (Nat.clog 2 xs.length) xs t (by rw [hs]; simp)

/-- The returned tree satisfies the ceiling-log backward-error bound.
This statement records its leaves explicitly; identifying their permutation
with the original input is a separate conservation obligation. -/
theorem algorithm_leaf_backward_error (xs : List ℝ) (err : ℕ → ℕ → ℝ)
    (hx : xs ≠ []) (u : ℝ) (hu : 0 ≤ u)
    (he : ∀ l j, |err l j| ≤ u)
    (hk : (Nat.clog 2 xs.length : ℝ) * u < 1) :
    ∃ t, algorithm xs err = some t ∧
      ∃ ps : List (ℝ × ℝ), ps.map Prod.fst = t.leaves ∧
        t.eval = (ps.map (fun p => p.1 + p.2)).sum ∧
        ∀ p ∈ ps, |p.2| ≤ gamma (Nat.clog 2 xs.length) u * |p.1| := by
  obtain ⟨t, ha, hd, hc⟩ := algorithm_coefficients xs err hx u hu he hk
  refine ⟨t, ha, t.terms.map (fun p => (p.1, p.1 * (p.2 - 1))), ?_, ?_, ?_⟩
  · simpa [List.map_map, Function.comp_def] using t.terms_inputs
  · rw [t.eval_terms, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p hp
    dsimp
    ring
  · intro p hp
    simp only [List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩
    dsimp
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hc q hq) (abs_nonneg _)

/-- Independent regression check of the offset and unchanged carry branch. -/
example :
    (level (fun _ => 0) ([2, 3, 4, 5, 6].map Tree.leaf)).map Tree.eval = [7, 9, 4] := by
  norm_num [level, Tree.eval]

example :
    (rounds (fun _ _ => 0) 3 ([2, 3, 4, 5, 6].map Tree.leaf)).map Tree.eval = [20] := by
  norm_num [rounds, level, Tree.eval]

end Bhola
