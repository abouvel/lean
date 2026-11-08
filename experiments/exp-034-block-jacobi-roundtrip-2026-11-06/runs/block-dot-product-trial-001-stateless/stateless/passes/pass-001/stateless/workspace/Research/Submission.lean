import Mathlib

/-!
Formal statement of Bhola's Block Dot Product theorem (source.txt).
Positive n and T make the source's logarithm and block partition well defined.
Local relative errors model arithmetic in the absence of overflow/underflow.
No bound on a global error or on the computed result is assumed.
-/
namespace BlockDotProduct

/-- Exact natural ceiling division, equal to ceil(n/T) when T > 0. -/
def blockCount (n T : ℕ) : ℕ := (n + T - 1) / T

/-- Exact ceiling binary logarithm; for positive m, the least d with m ≤ 2^d. -/
def reductionDepth (n T : ℕ) : ℕ := Nat.clog 2 (blockCount n T)

noncomputable def gamma (u : ℝ) (k : ℕ) : ℝ := (k : ℝ) * u / (1 - (k : ℝ) * u)

/-- Zero extension of the original input, including all unused final-block slots. -/
def padded {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  if h : k < n then x ⟨k, h⟩ else 0

/-- Operation-local relative errors. Multiplication and block addition addresses
are (block, slot); tree addition addresses are binary heap addresses rooted at 1. -/
structure RoundingErrors where
  mul : ℕ → ℕ → ℝ
  blockAdd : ℕ → ℕ → ℝ
  treeAdd : ℕ → ℝ

/-- The standard local floating-point model. Unused errors can be set to zero.
Every actual arithmetic operation below is its exact value times (1 + δ). -/
def RoundingErrors.Admissible (e : RoundingErrors) (u : ℝ) : Prop :=
  (∀ j t, |e.mul j t| ≤ u) ∧
  (∀ j t, |e.blockAdd j t| ≤ u) ∧
  (∀ a, |e.treeAdd a| ≤ u)

def roundedProduct {n : ℕ} (x y : Fin n → ℝ)
    (T : ℕ) (e : RoundingErrors) (j t : ℕ) : ℝ :=
  (padded x (j * T + t) * padded y (j * T + t)) * (1 + e.mul j t)

/-- Sequential accumulation of k products: the first product initializes the
accumulator, so there is no additional rounded addition to zero. -/
def blockPrefix {n : ℕ} (x y : Fin n → ℝ)
    (T : ℕ) (e : RoundingErrors) (j : ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 => roundedProduct x y T e j 0
  | k + 2 =>
      (blockPrefix x y T e j (k + 1) + roundedProduct x y T e j (k + 1)) *
        (1 + e.blockAdd j (k + 1))

def blockPartial {n : ℕ} (x y : Fin n → ℝ)
    (T : ℕ) (e : RoundingErrors) (j : ℕ) : ℝ :=
  blockPrefix x y T e j T

/-- A binary reduction schedule. `empty` only supports construction and carries:
valid schedules contain each real block exactly once. -/
inductive ReductionTree where
  | empty : ReductionTree
  | leaf : ℕ → ReductionTree
  | node : ReductionTree → ReductionTree → ReductionTree
  deriving Repr

def ReductionTree.leaves : ReductionTree → List ℕ
  | .empty => []
  | .leaf j => [j]
  | .node l r => l.leaves ++ r.leaves

def ReductionTree.height : ReductionTree → ℕ
  | .empty => 0
  | .leaf _ => 0
  | .node l r => max l.height r.height + 1

/-- Coverage is an algorithmic assumption: every partial occurs once. -/
def ValidSchedule (n T : ℕ) (tree : ReductionTree) : Prop :=
  tree.leaves.Perm (List.range (blockCount n T)) ∧
  tree.height ≤ reductionDepth n T

/-- Carry an unmatched subtree without performing an arithmetic operation. -/
def join : ReductionTree → ReductionTree → ReductionTree
  | .empty, r => r
  | l, .empty => l
  | l, r => .node l r

/-- Partition consecutive leaves into a balanced tree, pruning missing leaves. -/
def balancedTree (m : ℕ) : ℕ → ℕ → ReductionTree
  | 0, start => if start < m then .leaf start else .empty
  | d + 1, start =>
      join (balancedTree m d start) (balancedTree m d (start + 2 ^ d))

def canonicalTree (n T : ℕ) : ReductionTree :=
  balancedTree (blockCount n T) (reductionDepth n T) 0

/-- Evaluation performs one rounded addition at each binary node. -/
def evaluateTree (partials : ℕ → ℝ) (e : RoundingErrors) :
    ReductionTree → ℕ → ℝ
  | .empty, _ => 0
  | .leaf j, _ => partials j
  | .node l r, address =>
      (evaluateTree partials e l (2 * address) +
       evaluateTree partials e r (2 * address + 1)) * (1 + e.treeAdd address)

def computedResult {n : ℕ} (x y : Fin n → ℝ) (T : ℕ)
    (e : RoundingErrors) (tree : ReductionTree) : ℝ :=
  evaluateTree (blockPartial x y T e) e tree 1

lemma leaves_join (l r : ReductionTree) :
    (join l r).leaves = l.leaves ++ r.leaves := by
  cases l <;> cases r <;> simp [join, ReductionTree.leaves]

lemma height_join (l r : ReductionTree) :
    (join l r).height ≤ max l.height r.height + 1 := by
  cases l <;> cases r <;> simp [join, ReductionTree.height]

lemma balanced_leaves (m d s : ℕ) :
    (balancedTree m d s).leaves =
      (List.range' s (2^d)).filter (fun j => j < m) := by
  induction d generalizing s with
  | zero => simp [balancedTree, ReductionTree.leaves]; split <;> simp_all [ReductionTree.leaves]
  | succ d ih =>
    rw [balancedTree, leaves_join, ih, ih, ← List.filter_append]
    congr 1
    rw [pow_succ, Nat.mul_two]
    simpa using (List.range'_append (s := s) (m := 2^d) (n := 2^d))

lemma balanced_height (m d s : ℕ) : (balancedTree m d s).height ≤ d := by
  induction d generalizing s with
  | zero => simp [balancedTree]; split <;> simp [ReductionTree.height]
  | succ d ih =>
    exact (height_join _ _).trans (Nat.add_le_add_right (max_le (ih _) (ih _)) 1)

lemma filter_range_le (m L : ℕ) (h : m ≤ L) :
    (List.range L).filter (fun j => j < m) = List.range m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero =>
    simp only [Nat.add_zero]
    apply List.filter_eq_self.mpr
    simp
  | succ k ih =>
    rw [← Nat.add_assoc, List.range_succ, List.filter_append, ih (by omega)]
    simp

lemma canonical_valid_proof (n T : ℕ) : ValidSchedule n T (canonicalTree n T) := by
  constructor
  · unfold canonicalTree
    rw [balanced_leaves, ← List.range_eq_range', filter_range_le]
    exact Nat.le_pow_clog (by decide) _
  · exact balanced_height _ _ _

lemma abs_budget_add {u A a b a' b' v w δ : ℝ}
    (hu : 0 ≤ u) (hδ : |δ| ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hA : 1 ≤ A) (ha : |a| ≤ v) (hb : |b| ≤ w)
    (hea : |a' - a| ≤ (A-1)*v) (heb : |b' - b| ≤ (A-1)*w) :
    |(a'+b')*(1+δ) - (a+b)| ≤ (A*(1+u)-1)*(v+w) := by
  have hab : |a+b| ≤ v+w := (abs_add_le _ _).trans (add_le_add ha hb)
  have heab : |(a'-a)+(b'-b)| ≤ (A-1)*(v+w) := by
    calc
      _ ≤ |a'-a| + |b'-b| := abs_add_le _ _
      _ ≤ (A-1)*v + (A-1)*w := add_le_add hea heb
      _ = _ := by ring
  have hd : |1+δ| ≤ 1+u := by
    calc
      _ ≤ |(1:ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1+u := by simpa using add_le_add_left hδ 1
  calc
    _ = |((a'-a)+(b'-b))*(1+δ) + (a+b)*δ| := by congr 1; ring
    _ ≤ |((a'-a)+(b'-b))*(1+δ)| + |(a+b)*δ| := abs_add_le _ _
    _ = |(a'-a)+(b'-b)| *|1+δ| + |a+b| *|δ| := by rw [abs_mul, abs_mul]
    _ ≤ ((A-1)*(v+w))*(1+u) + (v+w)*u :=
      add_le_add (mul_le_mul heab hd (abs_nonneg _) (mul_nonneg (sub_nonneg.mpr hA) (add_nonneg hv hw)))
        (mul_le_mul hab hδ (abs_nonneg _) (by positivity))
    _ = _ := by ring

lemma budget_mono {u : ℝ} (hu : 0 ≤ u) {k l : ℕ} (h : k ≤ l) {M : ℝ}
    (hM : 0 ≤ M) :
    ((1+u)^k-1)*M ≤ ((1+u)^l-1)*M := by
  exact mul_le_mul_of_nonneg_right
    (sub_le_sub_right (pow_le_pow_right₀ (by linarith : 1 ≤ 1+u) h) 1) hM

lemma rounded_mul_bound {u a δ : ℝ} (hδ : |δ| ≤ u) :
    |a*(1+δ)-a| ≤ ((1+u)^1-1)*|a| := by
  calc
    _ = |a| *|δ| := by rw [show a*(1+δ)-a = a*δ by ring, abs_mul]
    _ ≤ |a| *u := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = _ := by ring

lemma abs_sum_range_le (f : ℕ → ℝ) (k : ℕ) :
    |∑ t ∈ Finset.range k, f t| ≤ ∑ t ∈ Finset.range k, |f t| :=
  Finset.abs_sum_le_sum_abs _ _

lemma block_error {n : ℕ} (x y : Fin n → ℝ) (T : ℕ)
    (e : RoundingErrors) (u : ℝ) (hu : 0 ≤ u) (he : e.Admissible u) (j k : ℕ) :
    |blockPrefix x y T e j k -
      ∑ t ∈ Finset.range k, padded x (j*T+t)*padded y (j*T+t)| ≤
      ((1+u)^k-1) *
      ∑ t ∈ Finset.range k, |padded x (j*T+t)*padded y (j*T+t)| := by
  let f := fun t => padded x (j*T+t)*padded y (j*T+t)
  change |blockPrefix x y T e j k - ∑ t ∈ Finset.range k, f t| ≤
    ((1+u)^k-1) * ∑ t ∈ Finset.range k, |f t|
  induction k using Nat.twoStepInduction with
  | zero => simp [blockPrefix]
  | one => simpa [blockPrefix, roundedProduct, f] using rounded_mul_bound (a := f 0) (he.1 j 0)
  | more k ih ih' =>
    rw [blockPrefix, Finset.sum_range_succ, Finset.sum_range_succ (fun t => |f t|)]
    have hp := rounded_mul_bound (a := f (k+1)) (he.1 j (k+1))
    have hp' : |roundedProduct x y T e j (k+1) - f (k+1)| ≤
        ((1+u)^(k+1)-1)*|f (k+1)| :=
      hp.trans (budget_mono hu (by omega) (abs_nonneg _))
    have H := abs_budget_add hu (he.2.1 j (k+1))
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (abs_nonneg (f (k+1)))
      (one_le_pow₀ (by linarith : 1 ≤ 1+u) (n := k+1))
      (abs_sum_range_le f (k+1)) (le_refl |f (k+1)|) ih' hp'
    simpa only [pow_succ] using H

lemma list_abs_bound (B M : ℕ → ℝ) (h : ∀ j, |B j| ≤ M j) (l : List ℕ) :
    |(l.map B).sum| ≤ (l.map M).sum := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simpa using (abs_add_le (B j) ((l.map B).sum)).trans (add_le_add (h j) ih)

lemma list_mass_nonneg (M : ℕ → ℝ) (h : ∀ j, 0 ≤ M j) (l : List ℕ) :
    0 ≤ (l.map M).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simpa using add_nonneg (h j) ih

lemma tree_error (P B M : ℕ → ℝ) (e : RoundingErrors) (u : ℝ)
    (hu : 0 ≤ u) (he : ∀ a, |e.treeAdd a| ≤ u) (T : ℕ)
    (hM : ∀ j, 0 ≤ M j) (hB : ∀ j, |B j| ≤ M j)
    (hP : ∀ j, |P j-B j| ≤ ((1+u)^T-1)*M j)
    (d : ℕ) (tree : ReductionTree) (hd : tree.height ≤ d) (a : ℕ) :
    |evaluateTree P e tree a - (tree.leaves.map B).sum| ≤
      ((1+u)^(T+d)-1) * (tree.leaves.map M).sum := by
  induction d generalizing tree a with
  | zero =>
    cases tree with
    | empty => simp [evaluateTree, ReductionTree.leaves]
    | leaf j => simpa [evaluateTree, ReductionTree.leaves] using hP j
    | node l r => simp [ReductionTree.height] at hd
  | succ d ih =>
    cases tree with
    | empty => simp [evaluateTree, ReductionTree.leaves]
    | leaf j =>
      simpa [evaluateTree, ReductionTree.leaves] using
        (hP j).trans (budget_mono hu (by omega) (hM j))
    | node l r =>
      have hl : l.height ≤ d := by simp [ReductionTree.height] at hd; omega
      have hr : r.height ≤ d := by simp [ReductionTree.height] at hd; omega
      have H := abs_budget_add hu (he a)
        (list_mass_nonneg M hM l.leaves) (list_mass_nonneg M hM r.leaves)
        (one_le_pow₀ (by linarith : 1 ≤ 1+u) (n := T+d))
        (list_abs_bound B M hB l.leaves) (list_abs_bound B M hB r.leaves)
        (ih l hl (2*a)) (ih r hr (2*a+1))
      simpa [evaluateTree, ReductionTree.leaves, List.map_append, List.sum_append,
        pow_succ, Nat.add_assoc] using H

/-- Elementary geometric growth bound on the admissible range. -/
lemma power_gamma (u : ℝ) (hu : 0 ≤ u) (k : ℕ) (hk : (k:ℝ)*u < 1) :
    (1+u)^k - 1 ≤ gamma u k := by
  have main : ∀ k : ℕ, (k:ℝ)*u < 1 → (1+u)^k * (1-(k:ℝ)*u) ≤ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro h
      have hk' : (k:ℝ)*u < 1 := by push_cast at h; nlinarith
      have H := ih hk'
      have hp : 0 ≤ (1+u)^k := by positivity
      have hstep : (1+u)*(1-((k+1:ℕ):ℝ)*u) ≤ 1-(k:ℝ)*u := by
        push_cast
        nlinarith [sq_nonneg u, mul_nonneg (show (0:ℝ) ≤ k by positivity) (sq_nonneg u)]
      calc
        (1+u)^(k+1)*(1-((k+1:ℕ):ℝ)*u) =
            (1+u)^k*((1+u)*(1-((k+1:ℕ):ℝ)*u)) := by rw [pow_succ]; ring
        _ ≤ (1+u)^k*(1-(k:ℝ)*u) := mul_le_mul_of_nonneg_left hstep hp
        _ ≤ 1 := H
  unfold gamma
  apply (le_div_iff₀ (by linarith : 0 < 1-(k:ℝ)*u)).mpr
  nlinarith [main k hk]


lemma sum_blocks (f : ℕ → ℝ) (m T : ℕ) :
    (∑ j ∈ Finset.range m, ∑ t ∈ Finset.range T, f (j*T+t)) =
      ∑ k ∈ Finset.range (m*T), f k := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]

lemma block_capacity (n T : ℕ) (hT : 0 < T) : n ≤ blockCount n T * T := by
  have H := Nat.div_add_mod (n+T-1) T
  have R := Nat.mod_lt (n+T-1) hT
  unfold blockCount
  rw [Nat.mul_comm T] at H
  omega

lemma padded_blocks {n : ℕ} (z : Fin n → ℝ) (T : ℕ) (hT : 0 < T) :
    (∑ j ∈ Finset.range (blockCount n T), ∑ t ∈ Finset.range T,
      padded z (j*T+t)) = ∑ i, z i := by
  rw [sum_blocks]
  have h : (∑ k ∈ Finset.range n, padded z k) =
      ∑ k ∈ Finset.range (blockCount n T*T), padded z k := by
    apply Finset.sum_subset
    · exact Finset.range_mono (block_capacity n T hT)
    · intro k hk hkn
      simp only [Finset.mem_range, not_lt] at hkn
      simp [padded, not_lt.mpr hkn]
  rw [← h, Finset.sum_fin_eq_sum_range]
  rfl

lemma padded_mul {n : ℕ} (x y : Fin n → ℝ) (k : ℕ) :
    padded (fun i => x i*y i) k = padded x k*padded y k := by
  unfold padded
  split <;> simp

lemma padded_abs {n : ℕ} (x : Fin n → ℝ) (k : ℕ) :
    padded (fun i => |x i|) k = |padded x k| := by
  unfold padded
  split <;> simp

lemma range_list_sum (f : ℕ → ℝ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ j ∈ Finset.range m, f j := by
  simpa only [List.toFinset_range] using (List.sum_toFinset f (List.nodup_range (n := m))).symm

lemma total_forward_error {n T : ℕ} (hT : 0 < T)
    (x y : Fin n → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (e : RoundingErrors) (he : e.Admissible u)
    (tree : ReductionTree) (htree : ValidSchedule n T tree)
    (hsmall : ((T + reductionDepth n T : ℕ) : ℝ) * u < 1) :
    |computedResult x y T e tree - ∑ i, x i*y i| ≤
      gamma u (T+reductionDepth n T) * ∑ i, |x i*y i| := by
  let B := fun j => ∑ t ∈ Finset.range T, padded x (j*T+t)*padded y (j*T+t)
  let M := fun j => ∑ t ∈ Finset.range T, |padded x (j*T+t)*padded y (j*T+t)|
  have hM : ∀ j, 0 ≤ M j := fun _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hB : ∀ j, |B j| ≤ M j := fun j => abs_sum_range_le _ _
  have H := tree_error (blockPartial x y T e) B M e u hu he.2.2 T hM hB
    (fun j => block_error x y T e u hu he j T)
    (reductionDepth n T) tree htree.2 1
  have hsumB : (tree.leaves.map B).sum = ∑ i, x i*y i := by
    rw [(htree.1.map B).sum_eq, range_list_sum]
    simp only [B, ← padded_mul]
    exact padded_blocks _ T hT
  have hsumM : (tree.leaves.map M).sum = ∑ i, |x i*y i| := by
    rw [(htree.1.map M).sum_eq, range_list_sum]
    simp only [M, ← padded_mul, ← padded_abs]
    exact padded_blocks _ T hT
  rw [hsumB, hsumM] at H
  exact H.trans (mul_le_mul_of_nonneg_right (power_gamma u hu _ hsmall)
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))


lemma backward_of_forward {n : ℕ} (x y : Fin n → ℝ) (r g : ℝ) (hg : 0 ≤ g)
    (hf : |r - ∑ i, x i*y i| ≤ g * ∑ i, |x i*y i|) :
    ∃ Δx Δy : Fin n → ℝ,
      r = ∑ i, (x i + Δx i)*y i ∧
      (∀ i, |Δx i| ≤ g*|x i|) ∧
      r = ∑ i, x i*(y i + Δy i) ∧
      (∀ i, |Δy i| ≤ g*|y i|) := by
  classical
  let S := ∑ i, |x i*y i|
  let E := r - ∑ i, x i*y i
  let c := E / S
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hf' : |E| ≤ g*S := hf
  have hc : |c| ≤ g := by
    by_cases hs : S = 0
    · simpa [c, hs] using hg
    · rw [show c = E/S from rfl, abs_div, abs_of_nonneg hS]
      exact (div_le_iff₀ (lt_of_le_of_ne hS (Ne.symm hs))).mpr hf'
  have hcS : c*S = E := by
    by_cases hs : S = 0
    · have hE : E = 0 := abs_eq_zero.mp (le_antisymm (by simpa [hs] using hf') (abs_nonneg E))
      simp [hs, hE]
    · exact div_mul_cancel₀ E hs
  let s : Fin n → ℝ := fun i => if x i*y i < 0 then -1 else 1
  have hsabs : ∀ i, |s i| = 1 := by
    intro i
    dsimp [s]
    split <;> norm_num
  have hsmul : ∀ i, s i*(x i*y i) = |x i*y i| := by
    intro i
    dsimp [s]
    split
    · next h => rw [abs_of_neg h]; ring
    · next h => rw [abs_of_nonneg (le_of_not_gt h)]; ring
  refine ⟨fun i => c*s i*x i, fun i => c*s i*y i, ?_, ?_, ?_, ?_⟩
  · have H : (∑ i, (x i+c*s i*x i)*y i) = (∑ i, x i*y i) + c*S := by
      calc
        _ = ∑ i, (x i*y i+c*|x i*y i|) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← hsmul i]
          ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [H, hcS]
    dsimp [E]
    ring
  · intro i
    simp only [abs_mul, hsabs, mul_one]
    exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  · have H : (∑ i, x i*(y i+c*s i*y i)) = (∑ i, x i*y i) + c*S := by
      calc
        _ = ∑ i, (x i*y i+c*|x i*y i|) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← hsmul i]
          ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [H, hcS]
    dsimp [E]
    ring
  · intro i
    simp only [abs_mul, hsabs, mul_one]
    exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)


/-- The concrete balanced schedule meets the paper's coverage and depth. -/
theorem canonicalTree_valid (n T : ℕ) (hn : 0 < n) (hT : 0 < T) :
    ValidSchedule n T (canonicalTree n T) := by
  exact canonical_valid_proof n T

/-- Full selected theorem, for every covering binary reduction schedule of the
specified depth and every admissible local rounding execution. Both backward
representations are supplied simultaneously, with the exact source constant. -/
theorem block_dot_product
    {n T : ℕ} (hn : 0 < n) (hT : 0 < T)
    (x y : Fin n → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (e : RoundingErrors) (he : e.Admissible u)
    (tree : ReductionTree) (htree : ValidSchedule n T tree)
    (hsmall : ((T + reductionDepth n T : ℕ) : ℝ) * u < 1) :
    ∃ Δx Δy : Fin n → ℝ,
      computedResult x y T e tree = ∑ i : Fin n, (x i + Δx i) * y i ∧
      (∀ i, |Δx i| ≤ gamma u (T + reductionDepth n T) * |x i|) ∧
      computedResult x y T e tree = ∑ i : Fin n, x i * (y i + Δy i) ∧
      (∀ i, |Δy i| ≤ gamma u (T + reductionDepth n T) * |y i|) := by
  apply backward_of_forward x y
  · unfold gamma
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)
  · exact total_forward_error hT x y u hu e he tree htree hsmall

/-- Concrete instantiation: no caller-supplied reduction schedule is required. -/
theorem block_dot_product_balanced
    {n T : ℕ} (hn : 0 < n) (hT : 0 < T)
    (x y : Fin n → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (e : RoundingErrors) (he : e.Admissible u)
    (hsmall : ((T + reductionDepth n T : ℕ) : ℝ) * u < 1) :
    ∃ Δx Δy : Fin n → ℝ,
      computedResult x y T e (canonicalTree n T) = ∑ i : Fin n, (x i + Δx i) * y i ∧
      (∀ i, |Δx i| ≤ gamma u (T + reductionDepth n T) * |x i|) ∧
      computedResult x y T e (canonicalTree n T) = ∑ i : Fin n, x i * (y i + Δy i) ∧
      (∀ i, |Δy i| ≤ gamma u (T + reductionDepth n T) * |y i|) := by
  exact block_dot_product hn hT x y u hu e he (canonicalTree n T)
    (canonicalTree_valid n T hn hT) hsmall

end BlockDotProduct
