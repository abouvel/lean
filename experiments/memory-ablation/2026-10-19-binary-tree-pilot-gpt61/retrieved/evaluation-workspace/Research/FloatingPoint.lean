import Research.BinaryTree

/-! An implementation parametrized by the actual deterministic floating-point
addition operation. The relative-error model is the sole numerical hypothesis;
absence of overflow and underflow is represented by its validity. -/
noncomputable section
namespace Bhola

/-- Number of active entries after round `d`. -/
def width (n d : ℕ) : ℕ := n ⌈/⌉ (2^d)

/-- Direct indexed implementation of Algorithm 1. Only indices below the active
width are read. The carry branch returns the previous value literally. -/
def run (fl : ℕ → ℕ → ℝ → ℝ → ℝ) (xs : List ℝ) : ℕ → ℕ → ℝ
  | 0, k => xs.getD k 0
  | d+1, k =>
    if k + width xs.length (d+1) < width xs.length d then
      fl d k (run fl xs d k) (run fl xs d (k + width xs.length (d+1)))
    else run fl xs d k

def sumFP (fl : ℕ → ℕ → ℝ → ℝ → ℝ) (xs : List ℝ) : ℝ :=
  run fl xs (depth xs) 0

/-- Standard relative-error addition model (equation (1) of the paper).
Round and node indices permit any deterministic implementation and error pattern. -/
def AdditionModel (u : ℝ) (fl : ℕ → ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∀ d k a b, ∃ e : ℝ, |e| ≤ u ∧ fl d k a b = (a+b)*(1+e)

def value (δ : ℕ → ℕ → ℝ) (xs : List ℝ) (d k : ℕ) : ℝ :=
  ((forest δ xs d).getD k (.leaf 0)).eval

lemma value_zero (δ xs k) : value δ xs 0 k = xs.getD k 0 := by
  simp [value, forest, Tree.eval]

lemma value_step (δ xs d k) (hk : k < width xs.length (d+1)) :
    value δ xs (d+1) k =
      if k + width xs.length (d+1) < width xs.length d then
        (value δ xs d k + value δ xs d (k + width xs.length (d+1))) * (1+δ d k)
      else value δ xs d k := by
  have hk' : k < half (forest δ xs d).length := by
    simpa [original_offset, width] using hk
  have hh := congrArg Tree.eval (round_getD (δ d) (forest δ xs d) k hk')
  rw [original_offset, forest_length] at hh
  simpa only [value, forest, width, apply_ite, Tree.eval] using hh

lemma width_mono (n d : ℕ) : width n (d+1) ≤ width n d := by
  have h := (half_bounds (forest (fun _ _ => 0) (List.replicate n (0:ℝ)) d).length).1
  rw [original_offset, forest_length] at h
  simpa only [List.length_replicate, width] using h

/-- Only additions actually executed need satisfy the relative-error model.
This is the paper's no-overflow/no-underflow assumption along this execution;
there is no assumption on other operands or on the unchanged carry branches. -/
def ExecutionModel (u : ℝ) (fl : ℕ → ℕ → ℝ → ℝ → ℝ) (xs : List ℝ) : Prop :=
  ∀ d k, d < depth xs → k < width xs.length (d+1) →
    k + width xs.length (d+1) < width xs.length d →
    ∃ e : ℝ, |e| ≤ u ∧
      fl d k (run fl xs d k) (run fl xs d (k + width xs.length (d+1))) =
        (run fl xs d k + run fl xs d (k + width xs.length (d+1)))*(1+e)

lemma AdditionModel.execution {u fl} (hm : AdditionModel u fl) (xs) :
    ExecutionModel u fl xs := by
  intro d k _ _ _
  exact hm d k _ _

/-- Every permitted execution is exactly the error-labelled tree execution. -/
theorem model_execution {u : ℝ} {fl : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hu : 0 ≤ u) {xs : List ℝ} (hm : ExecutionModel u fl xs) :
    ∃ δ : ℕ → ℕ → ℝ, (∀ d k, |δ d k| ≤ u) ∧
      ∀ d, d ≤ depth xs → ∀ k, k < width xs.length d →
        value δ xs d k = run fl xs d k := by
  have he : ∀ d k, ∃ e : ℝ, |e| ≤ u ∧
      (d < depth xs → k < width xs.length (d+1) →
        k + width xs.length (d+1) < width xs.length d →
        fl d k (run fl xs d k) (run fl xs d (k + width xs.length (d+1))) =
          (run fl xs d k + run fl xs d (k + width xs.length (d+1)))*(1+e)) := by
    intro d k
    by_cases hd : d < depth xs
    · by_cases hk : k < width xs.length (d+1)
      · by_cases hav : k + width xs.length (d+1) < width xs.length d
        · obtain ⟨e, hb, he⟩ := hm d k hd hk hav
          exact ⟨e, hb, fun _ _ _ => he⟩
        · exact ⟨0, by simpa using hu, fun _ _ h => (hav h).elim⟩
      · exact ⟨0, by simpa using hu, fun _ h _ => (hk h).elim⟩
    · exact ⟨0, by simpa using hu, fun h _ _ => (hd h).elim⟩
  choose δ hb heq using he
  refine ⟨δ, hb, ?_⟩
  intro d
  induction d with
  | zero => intro hd k hk; exact value_zero _ _ _
  | succ d ih =>
    intro hd k hk
    rw [value_step δ xs d k hk, run]
    split_ifs with hav
    · rw [ih (by omega) k (lt_of_lt_of_le hk (width_mono _ _)),
        ih (by omega) (k + width xs.length (d+1)) hav]
      exact (heq d k (by omega) hk hav).symm
    · exact ih (by omega) k (lt_of_lt_of_le hk (width_mono _ _))

/-- Theorem 3.1 for the direct deterministic implementation of Algorithm 1. -/
theorem theorem_3_1_floatingPoint {u : ℝ} {fl : ℕ → ℕ → ℝ → ℝ → ℝ}
    {xs : List ℝ} (hne : xs ≠ []) (hu : 0 ≤ u) (hm : ExecutionModel u fl xs)
    (hdu : (depth xs : ℝ)*u < 1) :
    ∃ Δ : Fin xs.length → ℝ,
      sumFP fl xs = ∑ i : Fin xs.length, (xs.get i + Δ i) ∧
      ∀ i, |Δ i| ≤ gamma u (depth xs)*|xs.get i| := by
  obtain ⟨δ, hb, hv⟩ := model_execution hu hm
  have hw : 0 < width xs.length (depth xs) := by
    have hh := final_length (δ := δ) hne
    rw [forest_length] at hh
    simp [width, hh]
  have hs : algorithm δ xs = sumFP fl xs := by
    have hh := hv (depth xs) le_rfl 0 hw
    have ht : (forest δ xs (depth xs)).headD (.leaf 0) =
        (forest δ xs (depth xs)).getD 0 (.leaf 0) := by
      cases forest δ xs (depth xs) <;> rfl
    simpa only [algorithm, value, sumFP, ht] using hh
  obtain ⟨Δ, heq, hΔ⟩ := theorem_3_1 hne hu hb hdu
  exact ⟨Δ, hs ▸ heq, hΔ⟩

/-- With exact additions, the direct implementation returns the exact sum. -/
theorem sumFP_exact {xs : List ℝ} (hne : xs ≠ []) :
    sumFP (fun _ _ a b => a+b) xs = xs.sum := by
  have hm : ExecutionModel 0 (fun _ _ a b => a+b) xs := by
    intro d k _ _ _
    exact ⟨0, by simp, by simp⟩
  obtain ⟨Δ, hs, hb⟩ := theorem_3_1_floatingPoint hne (le_refl 0) hm (by simp)
  have hz : ∀ i, Δ i = 0 := by
    intro i
    apply abs_eq_zero.mp
    exact le_antisymm (by simpa [gamma] using hb i) (abs_nonneg _)
  rw [hs]
  simp only [hz, add_zero]
  rw [← List.sum_ofFn, List.ofFn_get]

/-- A bundled complete specification: the actual deterministic execution has
all original leaves, exact logarithmic tree depth, and the componentwise bound. -/
theorem algorithm1_theorem3_1 {u : ℝ} {fl : ℕ → ℕ → ℝ → ℝ → ℝ}
    {xs : List ℝ} (hne : xs ≠ []) (hu : 0 ≤ u) (hm : ExecutionModel u fl xs)
    (hdu : (depth xs : ℝ)*u < 1) :
    ∃ (δ : ℕ → ℕ → ℝ) (t : Tree) (Δ : Fin xs.length → ℝ),
      (∀ d k, |δ d k| ≤ u) ∧
      forest δ xs (depth xs) = [t] ∧ t.leaves.Perm xs ∧
      t.height = Nat.clog 2 xs.length ∧
      sumFP fl xs = t.eval ∧
      sumFP fl xs = ∑ i : Fin xs.length, (xs.get i + Δ i) ∧
      ∀ i, |Δ i| ≤ gamma u (Nat.clog 2 xs.length)*|xs.get i| := by
  obtain ⟨δ, hb, hv⟩ := model_execution hu hm
  obtain ⟨t, ht, hp, hh, he⟩ := final_tree hne hb
  have hd : t.height = depth xs := by
    apply le_antisymm hh
    apply (depth_spec xs t.height).mpr
    rw [← hp.length_eq]
    exact t.leaf_count_le
  have hw : 0 < width xs.length (depth xs) := by
    have hh := final_length (δ := δ) hne
    rw [forest_length] at hh
    simp [width, hh]
  have hval : sumFP fl xs = t.eval := by
    have hr := hv (depth xs) le_rfl 0 hw
    simpa [sumFP, value, ht] using hr.symm
  obtain ⟨Δ, hsum, hbound⟩ := theorem_3_1 hne hu hb hdu
  refine ⟨δ, t, Δ, hb, ht, hp, hd, hval, ?_, hbound⟩
  rw [hval, ← he]
  exact hsum

end Bhola
