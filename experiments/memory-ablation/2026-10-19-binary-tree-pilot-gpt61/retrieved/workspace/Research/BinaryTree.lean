import Mathlib

/-! Algorithm 1 and Theorem 3.1 of Sahil Bhola.  Rounding errors are supplied
by a deterministic oracle indexed by round and position. Carries do not call
that oracle and are not rounded. `Nat.clog 2 n` is the exact ceiling logarithm. -/
noncomputable section
namespace Bhola

inductive Tree where
  | leaf (x : ℝ)
  | add (δ : ℝ) (left right : Tree)
  deriving Inhabited

def Tree.leaves : Tree → List ℝ
  | .leaf x => [x]
  | .add _ a b => a.leaves ++ b.leaves

def Tree.eval : Tree → ℝ
  | .leaf x => x
  | .add δ a b => (a.eval + b.eval) * (1 + δ)

inductive Good (u : ℝ) : ℕ → Tree → Prop
  | leaf (d x) : Good u d (.leaf x)
  | add {d δ a b} : |δ| ≤ u → Good u d a → Good u d b →
      Good u (d+1) (.add δ a b)

lemma Good.lift {u d t} (h : Good u d t) : Good u (d+1) t := by
  induction h with
  | leaf d x => exact .leaf _ _
  | add h ha hb iha ihb => exact .add h iha ihb

/-- Pair the first and second blocks at equal offsets, retaining the leftover
first-block entries literally unchanged. -/
def pair (δ : ℕ → ℝ) : ℕ → List Tree → List Tree → List Tree
  | _, [], _ => []
  | _, a :: as, [] => a :: as
  | k, a :: as, b :: bs => .add (δ k) a b :: pair δ (k+1) as bs

def half (n : ℕ) : ℕ := (n+1)/2

def round (δ : ℕ → ℝ) (ts : List Tree) : List Tree :=
  pair δ 0 (ts.take (half ts.length)) (ts.drop (half ts.length))

def forest (δ : ℕ → ℕ → ℝ) (xs : List ℝ) : ℕ → List Tree
  | 0 => xs.map Tree.leaf
  | d+1 => round (δ d) (forest δ xs d)

def depth (xs : List ℝ) : ℕ := Nat.clog 2 xs.length

def algorithm (δ : ℕ → ℕ → ℝ) (xs : List ℝ) : ℝ :=
  ((forest δ xs (depth xs)).headD (.leaf 0)).eval

def leaves (ts : List Tree) : List ℝ := (ts.map Tree.leaves).flatten

lemma pair_length (δ k as bs) (h : bs.length ≤ as.length) :
    (pair δ k as bs).length = as.length := by
  induction as generalizing k bs with
  | nil => simp_all [pair]
  | cons a as ih =>
    cases bs with
    | nil => simp [pair]
    | cons b bs => simpa [pair] using ih (k+1) bs (by simpa using h)

lemma half_bounds (n : ℕ) : half n ≤ n ∧ n - half n ≤ half n := by
  unfold half
  omega

lemma round_length (δ ts) : (round δ ts).length = half ts.length := by
  unfold round
  rw [pair_length, List.length_take, Nat.min_eq_left (half_bounds _).1]
  simp only [List.length_drop, List.length_take]
  rw [Nat.min_eq_left (half_bounds _).1]
  exact (half_bounds _).2

lemma pair_good {u d δ k as bs} (hδ : ∀ k, |δ k| ≤ u)
    (ha : ∀ t ∈ as, Good u d t) (hb : ∀ t ∈ bs, Good u d t) :
    ∀ t ∈ pair δ k as bs, Good u (d+1) t := by
  induction as generalizing k bs with
  | nil => simp [pair]
  | cons a as ih =>
    cases bs with
    | nil => simpa [pair] using fun t ht => (ha t ht).lift
    | cons b bs =>
      simp only [pair, List.mem_cons]
      intro t ht
      rcases ht with rfl | ht
      · exact .add (hδ _) (ha _ (by simp)) (hb _ (by simp))
      · exact ih (k := k+1) (bs := bs) (fun t ht => ha t (by simp [ht]))
          (fun t ht => hb t (by simp [ht])) t ht

lemma forest_good {u δ xs} (hδ : ∀ d k, |δ d k| ≤ u) (d) :
    ∀ t ∈ forest δ xs d, Good u d t := by
  induction d with
  | zero => simp only [forest, List.mem_map]; rintro t ⟨x, _, rfl⟩; exact .leaf _ _
  | succ d ih =>
    apply pair_good (hδ d)
    · exact fun t ht => ih t (List.mem_of_mem_take ht)
    · exact fun t ht => ih t (List.mem_of_mem_drop ht)

lemma pair_leaves (δ k as bs) (h : bs.length ≤ as.length) :
    (leaves (pair δ k as bs)).Perm (leaves as ++ leaves bs) := by
  induction as generalizing k bs with
  | nil => cases bs <;> simp_all [pair, leaves]
  | cons a as ih =>
    cases bs with
    | nil => simp [pair, leaves]
    | cons b bs =>
      have hp := ih (k+1) bs (by simpa using h)
      simp only [pair, leaves, List.map_cons, List.flatten_cons, Tree.leaves] at *
      have hp' := hp.append_left (a.leaves ++ b.leaves)
      apply hp'.trans
      simpa only [List.append_assoc] using
        ((List.perm_append_comm : (b.leaves ++ leaves as).Perm (leaves as ++ b.leaves)).append_left a.leaves).append_right (leaves bs)

lemma round_leaves (δ ts) : (leaves (round δ ts)).Perm (leaves ts) := by
  have h := pair_leaves δ 0 (ts.take (half ts.length)) (ts.drop (half ts.length))
    (by simp only [List.length_take, List.length_drop];
        rw [Nat.min_eq_left (half_bounds _).1]; exact (half_bounds _).2)
  simpa [round, leaves, ← List.map_append, ← List.flatten_append] using h

lemma forest_leaves (δ xs d) : (leaves (forest δ xs d)).Perm xs := by
  induction d with
  | zero =>
    suffices leaves (xs.map Tree.leaf) = xs by simp [forest, this]
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa [leaves, Tree.leaves] using congrArg (List.cons x) ih
  | succ d ih => exact (round_leaves _ _).trans ih

/-- A convenient polynomial error bound, subsequently bounded by gamma. -/
def B (u : ℝ) : ℕ → ℝ
  | 0 => 0
  | d+1 => B u d * (1+u) + u

lemma B_nonneg {u : ℝ} (hu : 0 ≤ u) (d) : 0 ≤ B u d := by
  induction d with
  | zero => simp [B]
  | succ d ih => exact add_nonneg (mul_nonneg ih (by linarith)) hu

lemma local_error {u e x z : ℝ} {d : ℕ} (hu : 0 ≤ u) (he : |e| ≤ u)
    (hz : |z-x| ≤ B u d * |x|) :
    |z*(1+e)-x| ≤ B u (d+1)*|x| := by
  have h1 : |1+e| ≤ 1+u := (abs_add_le 1 e).trans (by simpa using he)
  calc
    |z*(1+e)-x| = |(z-x)*(1+e)+x*e| := by congr 1; ring
    _ ≤ |z-x| *|1+e|+|x| *|e| := by simpa [abs_mul] using abs_add_le ((z-x)*(1+e)) (x*e)
    _ ≤ (B u d*|x|)*(1+u)+|x| *u := by
      have := B_nonneg hu d
      gcongr
    _ = B u (d+1)*|x| := by simp [B]; ring

lemma good_backward {u : ℝ} (hu : 0 ≤ u) {d t} (h : Good u d t) :
    ∃ ys : List ℝ, List.Forall₂ (fun x y => |y-x| ≤ B u d*|x|) t.leaves ys ∧
      ys.sum = t.eval := by
  induction h with
  | leaf d x =>
    refine ⟨[x], .cons ?_ .nil, by simp [Tree.eval]⟩
    simpa using mul_nonneg (B_nonneg hu d) (abs_nonneg x)
  | @add d e a b he ha hb iha ihb =>
    obtain ⟨ya, hya, esa⟩ := iha
    obtain ⟨yb, hyb, esb⟩ := ihb
    refine ⟨(ya ++ yb).map (fun y => y*(1+e)), ?_, ?_⟩
    · have hh := List.rel_append hya hyb
      have hs : ∀ {xs ys : List ℝ},
          List.Forall₂ (fun x y => |y-x| ≤ B u d * |x|) xs ys →
          List.Forall₂ (fun x y => |y-x| ≤ B u (d+1) * |x|)
            xs (ys.map (fun y => y*(1+e))) := by
        intro xs ys h
        induction h with
        | nil => exact .nil
        | cons hxy hrest ih => exact .cons (local_error hu he hxy) ih
      exact hs hh
    · simp [List.sum_map_mul_right, List.sum_append, esa, esb, Tree.eval]
      ring

def gamma (u : ℝ) (d : ℕ) : ℝ := (d:ℝ)*u / (1-(d:ℝ)*u)

lemma B_le_gamma {u : ℝ} (hu : 0 ≤ u) {d : ℕ} (hd : (d:ℝ)*u < 1) :
    B u d ≤ gamma u d := by
  have key : ∀ d : ℕ, (d:ℝ)*u < 1 → B u d * (1-(d:ℝ)*u) ≤ (d:ℝ)*u := by
    intro d
    induction d with
    | zero => simp [B]
    | succ d ih =>
      intro hs
      have hc : ((d+1:ℕ):ℝ) = (d:ℝ)+1 := by simp
      rw [hc] at hs ⊢
      have hd' : (d:ℝ)*u < 1 := by nlinarith
      have hi := ih hd'
      have hb := B_nonneg hu d
      have hn : 0 ≤ (d:ℝ)*u := mul_nonneg (Nat.cast_nonneg _) hu
      simp only [B]
      nlinarith [mul_nonneg (mul_nonneg hb hn) hu,
        mul_nonneg hb (sq_nonneg u),
        mul_nonneg (show 0 ≤ (d:ℝ)+1 by positivity) (sq_nonneg u)]
  exact (le_div_iff₀ (by linarith : 0 < 1-(d:ℝ)*u)).2 (key d hd)

/-- The ceiling division law makes the round schedule equal to the paper's
original offsets, including non-powers of two. -/
lemma ceilDiv_twice (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (n ⌈/⌉ a) ⌈/⌉ b = n ⌈/⌉ (a*b) := by
  apply eq_of_forall_ge_iff
  intro k
  rw [ceilDiv_le_iff_le_mul hb, ceilDiv_le_iff_le_mul ha,
    ceilDiv_le_iff_le_mul (Nat.mul_pos ha hb)]
  simp [Nat.mul_assoc]

lemma half_eq_ceilDiv (n : ℕ) : half n = n ⌈/⌉ 2 := by
  simp [half, Nat.ceilDiv_eq_add_pred_div]

lemma forest_length (δ xs d) :
    (forest δ xs d).length = xs.length ⌈/⌉ (2^d) := by
  induction d with
  | zero => simp [forest]
  | succ d ih =>
    rw [forest, round_length, ih, half_eq_ceilDiv,
      ceilDiv_twice _ _ _ (by positivity) (by omega), pow_succ]

/-- At round `d`, the offset is exactly ceil(n / 2^(d+1)). -/
lemma original_offset (δ xs d) :
    half (forest δ xs d).length = xs.length ⌈/⌉ (2^(d+1)) := by
  rw [forest_length, half_eq_ceilDiv,
    ceilDiv_twice _ _ _ (by positivity) (by omega), pow_succ]

lemma depth_spec (xs : List ℝ) (d : ℕ) :
    depth xs ≤ d ↔ xs.length ≤ 2^d :=
  Nat.clog_le_iff_le_pow (by omega)

lemma final_length {δ xs} (hne : xs ≠ []) :
    (forest δ xs (depth xs)).length = 1 := by
  rw [forest_length]
  have hp : 0 < 2^(depth xs) := by positivity
  have hn : 0 < xs.length := List.length_pos_iff.mpr hne
  have hle : xs.length ⌈/⌉ (2^depth xs) ≤ 1 :=
    (ceilDiv_le_iff_le_mul hp).mpr (by simpa using (depth_spec xs (depth xs)).mp le_rfl)
  have hnot : ¬ xs.length ⌈/⌉ (2^depth xs) ≤ 0 := by
    rw [ceilDiv_le_iff_le_mul hp]
    simp only [mul_zero, nonpos_iff_eq_zero]
    omega
  omega

/-- Theorem 3.1 in an occurrence-preserving list form. `ys` consists of the
perturbed inputs in the original order, including repeated and zero entries. -/
theorem theorem_3_1_list {u : ℝ} {δ : ℕ → ℕ → ℝ} {xs : List ℝ}
    (hne : xs ≠ []) (hu : 0 ≤ u)
    (hδ : ∀ d k, |δ d k| ≤ u) (hdu : (depth xs : ℝ)*u < 1) :
    ∃ ys : List ℝ,
      List.Forall₂ (fun x y => |y-x| ≤ gamma u (depth xs)*|x|) xs ys ∧
      algorithm δ xs = ys.sum := by
  obtain ⟨t, ht⟩ := List.length_eq_one_iff.mp (final_length (δ := δ) hne)
  have hg : Good u (depth xs) t := forest_good hδ _ t (by rw [ht]; simp)
  obtain ⟨ys, hy, hs⟩ := good_backward hu hg
  have hp : xs.Perm t.leaves := by
    have hh := forest_leaves δ xs (depth xs)
    simpa [ht, leaves] using hh.symm
  obtain ⟨zs, hz, hpz⟩ := List.perm_comp_forall₂ hp hy
  refine ⟨zs, ?_, ?_⟩
  · exact List.Forall₂.imp (fun x y h => h.trans (mul_le_mul_of_nonneg_right
      (B_le_gamma hu hdu) (abs_nonneg x))) hz
  · have he : algorithm δ xs = t.eval := by simp [algorithm, ht]
    rw [he, ← hs]
    exact hpz.sum_eq.symm

/-- Theorem 3.1, with a separate perturbation for every input occurrence. -/
theorem theorem_3_1 {u : ℝ} {δ : ℕ → ℕ → ℝ} {xs : List ℝ}
    (hne : xs ≠ []) (hu : 0 ≤ u)
    (hδ : ∀ d k, |δ d k| ≤ u) (hdu : (depth xs : ℝ)*u < 1) :
    ∃ Δ : Fin xs.length → ℝ,
      algorithm δ xs = ∑ i : Fin xs.length, (xs.get i + Δ i) ∧
      ∀ i, |Δ i| ≤ gamma u (depth xs)*|xs.get i| := by
  obtain ⟨ys, hy, hs⟩ := theorem_3_1_list hne hu hδ hdu
  let y : Fin xs.length → ℝ := fun i => ys.get (Fin.cast hy.length_eq i)
  refine ⟨fun i => y i - xs.get i, ?_, ?_⟩
  · have hlist : List.ofFn y = ys := by
      apply List.ext_get (by simp [hy.length_eq])
      intro i h1 h2
      simp [y]
    calc
      algorithm δ xs = ys.sum := hs
      _ = ∑ i : Fin xs.length, y i := by rw [← List.sum_ofFn, hlist]
      _ = ∑ i : Fin xs.length, (xs.get i + (y i - xs.get i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
  · intro i
    exact hy.get i.isLt (by simpa [hy.length_eq] using i.isLt)

/-- The longest path counts additions only; carries introduce no nodes. -/
def Tree.height : Tree → ℕ
  | .leaf _ => 0
  | .add _ a b => max a.height b.height + 1

lemma Good.height_le {u d t} (h : Good u d t) : t.height ≤ d := by
  induction h with
  | leaf d x => exact Nat.zero_le _
  | add he ha hb iha ihb => simpa [Tree.height] using Nat.succ_le_succ (max_le iha ihb)

lemma Tree.leaf_count_le (t : Tree) : t.leaves.length ≤ 2^t.height := by
  induction t with
  | leaf x => simp [Tree.leaves, Tree.height]
  | add e a b iha ihb =>
    have ha : 2^a.height ≤ 2^(max a.height b.height) :=
      Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have hb : 2^b.height ≤ 2^(max a.height b.height) :=
      Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    simp only [Tree.leaves, List.length_append, Tree.height, pow_succ]
    omega

/-- The returned tree contains precisely all inputs (with multiplicity), and
no input passes through more than the stated ceiling logarithm of additions. -/
theorem final_tree {u : ℝ} {δ : ℕ → ℕ → ℝ} {xs : List ℝ}
    (hne : xs ≠ []) (hδ : ∀ d k, |δ d k| ≤ u) :
    ∃ t, forest δ xs (depth xs) = [t] ∧ t.leaves.Perm xs ∧
      t.height ≤ depth xs ∧ algorithm δ xs = t.eval := by
  obtain ⟨t, ht⟩ := List.length_eq_one_iff.mp (final_length (δ := δ) hne)
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · simpa [ht, leaves] using forest_leaves δ xs (depth xs)
  · exact (forest_good (xs := xs) hδ (depth xs) t (by rw [ht]; simp)).height_le
  · simp [algorithm, ht]

/-- Exact arithmetic specialization: Algorithm 1 sums every occurrence. -/
theorem algorithm_exact {xs : List ℝ} (hne : xs ≠ []) :
    algorithm (fun _ _ => 0) xs = xs.sum := by
  obtain ⟨ys, hy, hs⟩ := theorem_3_1_list (u := 0) (δ := fun _ _ => 0) hne (by rfl)
    (by intros; simp) (by simp)
  have he : List.Forall₂ Eq xs ys := List.Forall₂.imp (fun x y h => by
    have hh : |y-x| = 0 := le_antisymm (by simpa [gamma] using h) (abs_nonneg _)
    exact (sub_eq_zero.mp (abs_eq_zero.mp hh)).symm) hy
  have hxy : xs = ys := by rwa [List.forall₂_eq_eq_eq] at he
  simpa [← hxy] using hs

/-- A pointwise specification of the two branches of offset pairing.
Indices here are zero based; `k+i` corresponds to the paper's `k+i+1`. -/
lemma pair_getD (δ k as bs) (h : bs.length ≤ as.length) (i : ℕ)
    (hi : i < as.length) :
    (pair δ k as bs).getD i (.leaf 0) =
      if i < bs.length then
        .add (δ (k+i)) (as.getD i (.leaf 0)) (bs.getD i (.leaf 0))
      else as.getD i (.leaf 0) := by
  induction as generalizing k bs i with
  | nil => simp at hi
  | cons a as ih =>
    cases bs with
    | nil => simp [pair]
    | cons b bs =>
      cases i with
      | zero => simp [pair]
      | succ i =>
        simpa [pair, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (k+1) bs (by simpa using h) i (by simpa using hi)

/-- Algorithm 1, lines 5--9: pair `i` with `i+offset` when available;
otherwise retain the existing entry unchanged, with no extra rounding. -/
theorem round_getD (δ ts i) (hi : i < half ts.length) :
    (round δ ts).getD i (.leaf 0) =
      if i + half ts.length < ts.length then
        .add (δ i) (ts.getD i (.leaf 0))
          (ts.getD (i + half ts.length) (.leaf 0))
      else ts.getD i (.leaf 0) := by
  have h := pair_getD δ 0 (ts.take (half ts.length)) (ts.drop (half ts.length))
    (by simp only [List.length_take, List.length_drop];
        rw [Nat.min_eq_left (half_bounds _).1]; exact (half_bounds _).2) i
    (by simp [List.length_take, Nat.min_eq_left (half_bounds _).1]; exact hi)
  have hc : i < (ts.drop (half ts.length)).length ↔ i + half ts.length < ts.length := by
    simp only [List.length_drop]
    omega
  simpa only [round, hc, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hi, List.getElem?_drop, Nat.zero_add, Nat.add_comm] using h

/-- The longest leaf-to-root addition path has exactly ceiling-logarithmic depth. -/
theorem exact_depth {u : ℝ} {δ : ℕ → ℕ → ℝ} {xs : List ℝ}
    (hne : xs ≠ []) (hδ : ∀ d k, |δ d k| ≤ u) :
    ∃ t, forest δ xs (depth xs) = [t] ∧ t.height = depth xs := by
  obtain ⟨t, ht, hp, hh, _⟩ := final_tree hne hδ
  refine ⟨t, ht, le_antisymm hh ?_⟩
  apply (depth_spec xs t.height).mpr
  rw [← hp.length_eq]
  exact t.leaf_count_le

end Bhola
