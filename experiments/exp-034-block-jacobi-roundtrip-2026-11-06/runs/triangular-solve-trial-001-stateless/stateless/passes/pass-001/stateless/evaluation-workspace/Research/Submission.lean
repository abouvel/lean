import Mathlib
import Research.Bounds

/-!
Formalization of Bhola, `theorem:solution_of_a_traingular_system`.
The relative-error hypotheses below concern exactly the operations in the
constructed execution; they do not assume a backward-error certificate.
The proof derives row residual bounds from the constructed execution trace.
-/

namespace TriangularSolve

/-- The source's deterministic error constant, with the same dimension. -/
noncomputable def gamma (n : ℕ) (u : ℝ) : ℝ := (n : ℝ) * u / (1 - (n : ℝ) * u)

inductive Operation where
  | add | sub | mul | div
  deriving DecidableEq

/-- Real-valued results returned by the floating-point arithmetic implementation. -/
structure Arithmetic where
  add : ℝ → ℝ → ℝ
  sub : ℝ → ℝ → ℝ
  mul : ℝ → ℝ → ℝ
  div : ℝ → ℝ → ℝ

/-- An elementary operation together with its actual operands. -/
structure Call where
  operation : Operation
  left : ℝ
  right : ℝ

noncomputable def Call.exact (c : Call) : ℝ :=
  match c.operation with
  | .add => c.left + c.right
  | .sub => c.left - c.right
  | .mul => c.left * c.right
  | .div => c.left / c.right

def Call.computed (c : Call) (ar : Arithmetic) : ℝ :=
  match c.operation with
  | .add => ar.add c.left c.right
  | .sub => ar.sub c.left c.right
  | .mul => ar.mul c.left c.right
  | .div => ar.div c.left c.right

/-- The no-overflow/no-underflow relative-error model at one executed operation.
For division it is required only at nonzero divisors. Nonzero pivots must be
proved from triangularity and nonsingularity, rather than assumed here. -/
def Call.SatisfiesModel (c : Call) (ar : Arithmetic) (u : ℝ) : Prop :=
  (c.operation = .div → c.right ≠ 0) →
    ∃ δ : ℝ, |δ| ≤ u ∧ c.computed ar = c.exact * (1 + δ)

/-- An actual computed value and the elementary operations used to obtain it. -/
structure Execution (α : Type) where
  value : α
  calls : List Call

def perform (ar : Arithmetic) (op : Operation) (a b : ℝ) : Execution ℝ :=
  let c : Call := ⟨op, a, b⟩
  ⟨c.computed ar, [c]⟩

/-- Continue a left-to-right inner product after its first product. -/
def dotTail (ar : Arithmetic) : Execution ℝ → List (ℝ × ℝ) → Execution ℝ
  | acc, [] => acc
  | acc, (a, b) :: rest =>
    let p := perform ar .mul a b
    let s := perform ar .add acc.value p.value
    dotTail ar ⟨s.value, acc.calls ++ p.calls ++ s.calls⟩ rest

/-- Sequential inner product: the first product initializes the accumulator,
so there is no rounded addition to zero. An empty inner product is exact zero. -/
def sequentialDot (ar : Arithmetic) : List (ℝ × ℝ) → Execution ℝ
  | [] => ⟨0, []⟩
  | (a, b) :: rest => dotTail ar (perform ar .mul a b) rest

/-- One forward-substitution row, with a single division for the first row. -/
def forwardRow {n : ℕ} (ar : Arithmetic) (T : Matrix (Fin n) (Fin n) ℝ)
    (b x : Fin n → ℝ) (i : Fin n) : Execution ℝ :=
  if i.val = 0 then
    perform ar .div (b i) (T i i)
  else
    let terms := ((List.finRange n).filter (fun j => j < i)).map
      (fun j => (T i j, x j))
    let p := sequentialDot ar terms
    let s := perform ar .sub (b i) p.value
    let q := perform ar .div s.value (T i i)
    ⟨q.value, p.calls ++ s.calls ++ q.calls⟩

/-- Store the next computed component and append its actual operation trace. -/
noncomputable def forwardStep {n : ℕ} (ar : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (state : Execution (Fin n → ℝ)) (i : Fin n) : Execution (Fin n → ℝ) :=
  let row := forwardRow ar T b state.value i
  ⟨Function.update state.value i row.value, state.calls ++ row.calls⟩

/-- Forward substitution in increasing row order. The fold also handles n = 0. -/
noncomputable def forwardSubstitution {n : ℕ} (ar : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : Execution (Fin n → ℝ) :=
  (List.finRange n).foldl (forwardStep ar T b) ⟨fun _ => 0, []⟩

/-- Simultaneous reversal of matrix rows and columns. -/
def reverseMatrix {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => T i.rev j.rev

/-- Reversal of a vector. -/
def reverseVector {n : ℕ} (b : Fin n → ℝ) : Fin n → ℝ := fun i => b i.rev

/-- Backward substitution visits rows n-1,...,0 and accumulates each row's
inner product in the dependency order n-1,...,i+1. -/
noncomputable def backwardSubstitution {n : ℕ} (ar : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : Execution (Fin n → ℝ) :=
  let run := forwardSubstitution ar (reverseMatrix T) (reverseVector b)
  ⟨reverseVector run.value, run.calls⟩

inductive Direction where
  | lower | upper
  deriving DecidableEq

/-- Lower or upper triangular support, including an unrestricted diagonal. -/
def IsTriangular {n : ℕ} (direction : Direction)
    (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  match direction with
  | .lower => ∀ i j, i < j → T i j = 0
  | .upper => ∀ i j, j < i → T i j = 0

noncomputable def substitution {n : ℕ} (direction : Direction) (ar : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : Execution (Fin n → ℝ) :=
  match direction with
  | .lower => forwardSubstitution ar T b
  | .upper => backwardSubstitution ar T b

/-- The source rounding model holds throughout this execution. No global
assumptions on unused operands, row error bounds, or perturbed equations occur. -/
def Execution.SatisfiesModel {α : Type} (run : Execution α) (ar : Arithmetic)
    (u : ℝ) : Prop :=
  ∀ c ∈ run.calls, c.SatisfiesModel ar u

private lemma dotTail_calls (ar : Arithmetic) (acc : Execution ℝ)
    (xs : List (ℝ × ℝ)) : ∀ c ∈ acc.calls, c ∈ (dotTail ar acc xs).calls := by
  induction xs generalizing acc with
  | nil => simp [dotTail]
  | cons ab xs ih =>
    intro c hc
    apply ih
    simp only [List.mem_append]
    exact Or.inl (Or.inl hc)

private lemma dotTail_error (ar : Arithmetic) (u : ℝ) (hu : 0 ≤ u)
    (xs : List (ℝ × ℝ)) (acc : Execution ℝ) (m : ℕ) (s A : ℝ)
    (hm : 1 ≤ m) (hA : 0 ≤ A) (hs : |s| ≤ A)
    (herr : |acc.value-s| ≤ TriangularSolveBounds.g m u*A)
    (hn : ((m+xs.length:ℕ):ℝ)*u < 1)
    (hr : (dotTail ar acc xs).SatisfiesModel ar u) :
    |(dotTail ar acc xs).value - (s+(xs.map (fun ab => ab.1*ab.2)).sum)| ≤
      TriangularSolveBounds.g (m+xs.length) u * (A+(xs.map (fun ab => |ab.1*ab.2|)).sum) := by
  induction xs generalizing acc m s A with
  | nil => simpa [dotTail] using herr
  | cons ab xs ih =>
    rcases ab with ⟨a,b⟩
    let p := perform ar .mul a b
    let q := perform ar .add acc.value p.value
    let next : Execution ℝ := ⟨q.value, acc.calls ++ p.calls ++ q.calls⟩
    have hm1 : ((m+1:ℕ):ℝ)*u < 1 := by
      apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right _ hu) hn
      exact_mod_cast (show m+1 ≤ m+((a,b)::xs).length by simp)
    have hp : (⟨.mul,a,b⟩ : Call).SatisfiesModel ar u := by
      apply hr
      apply dotTail_calls ar next xs
      simp [next,p,perform]
    have hq : (⟨.add,acc.value,p.value⟩ : Call).SatisfiesModel ar u := by
      apply hr
      apply dotTail_calls ar next xs
      simp [next,q,perform]
    obtain ⟨δ,hδ,eδ⟩ : ∃ δ : ℝ, |δ| ≤ u ∧ p.value = a*b*(1+δ) := by
      simpa [Call.SatisfiesModel, Call.computed, Call.exact, p, perform] using hp
    obtain ⟨ε,hε,eε⟩ : ∃ ε : ℝ, |ε| ≤ u ∧ q.value = (acc.value+p.value)*(1+ε) := by
      simpa [Call.SatisfiesModel, Call.computed, Call.exact, q, perform] using hq
    have hp_err : |p.value-a*b| ≤ u*|a*b| := by
      rw [eδ, show a*b*(1+δ)-a*b = (a*b)*δ by ring, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left hδ (abs_nonneg (a*b))]
    have hac : |acc.value| ≤ (1+TriangularSolveBounds.g m u)*A := by
      have := abs_add_le (acc.value-s) s
      rw [sub_add_cancel] at this
      nlinarith
    have hpc : |p.value| ≤ (1+u)*|a*b| := by
      have := abs_add_le (p.value-a*b) (a*b)
      rw [sub_add_cancel] at this
      nlinarith
    have hsum : |acc.value+p.value| ≤ (1+TriangularSolveBounds.g m u)*A+(1+u)*|a*b| :=
      (abs_add_le _ _).trans (add_le_add hac hpc)
    have hlocal : |q.value-(s+a*b)| ≤ TriangularSolveBounds.g (m+1) u*(A+|a*b|) := by
      have hid : q.value-(s+a*b) = (acc.value-s)+(p.value-a*b)+ε*(acc.value+p.value) := by rw [eε]; ring
      rw [hid]
      have h1 := abs_add_le ((acc.value-s)+(p.value-a*b)) (ε*(acc.value+p.value))
      have h2 := abs_add_le (acc.value-s) (p.value-a*b)
      have h3 : |ε*(acc.value+p.value)| ≤ u*((1+TriangularSolveBounds.g m u)*A+(1+u)*|a*b|) := by
        rw [abs_mul]
        exact mul_le_mul hε hsum (abs_nonneg _) hu
      have hg := mul_le_mul_of_nonneg_right (TriangularSolveBounds.g_step hu hm1) hA
      have hg2 := mul_le_mul_of_nonneg_right (TriangularSolveBounds.two_round hu hm hm1) (abs_nonneg (a*b))
      linarith
    have hs' : |s+a*b| ≤ A+|a*b| := (abs_add_le _ _).trans (add_le_add hs le_rfl)
    have hresult := ih next (m+1) (s+a*b) (A+|a*b|) (by omega)
      (by positivity) hs' hlocal (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn) hr
    simpa [dotTail, next, p, q, List.map_cons, List.sum_cons, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm, add_assoc] using hresult

private lemma sequentialDot_error (ar : Arithmetic) (u : ℝ) (hu : 0 ≤ u)
    (xs : List (ℝ × ℝ)) (hn : (xs.length:ℝ)*u < 1)
    (hr : (sequentialDot ar xs).SatisfiesModel ar u) :
    |(sequentialDot ar xs).value - (xs.map (fun ab => ab.1*ab.2)).sum| ≤
      TriangularSolveBounds.g xs.length u * (xs.map (fun ab => |ab.1*ab.2|)).sum := by
  cases xs with
  | nil => simp [sequentialDot, TriangularSolveBounds.g]
  | cons ab xs =>
    rcases ab with ⟨a,b⟩
    have hp : (⟨.mul,a,b⟩ : Call).SatisfiesModel ar u := by
      apply hr
      apply dotTail_calls ar (perform ar .mul a b) xs
      simp [perform]
    obtain ⟨δ,hδ,eδ⟩ : ∃ δ : ℝ, |δ| ≤ u ∧ (perform ar .mul a b).value = a*b*(1+δ) := by
      simpa [Call.SatisfiesModel, Call.computed, Call.exact, perform] using hp
    have hu1 : u < 1 := by
      have : (1:ℝ)*u ≤ (((a,b)::xs).length:ℝ)*u := mul_le_mul_of_nonneg_right (by exact_mod_cast (show 1 ≤ ((a,b)::xs).length by simp)) hu
      linarith
    have hg : u ≤ TriangularSolveBounds.g 1 u := by
      unfold TriangularSolveBounds.g
      norm_num
      apply (le_div_iff₀ (by linarith : 0 < 1-u)).2
      nlinarith [sq_nonneg u]
    have herr : |(perform ar .mul a b).value-a*b| ≤ TriangularSolveBounds.g 1 u*|a*b| := by
      rw [eδ, show a*b*(1+δ)-a*b = a*b*δ by ring, abs_mul]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hδ.trans hg) (abs_nonneg (a*b))
    have h := dotTail_error ar u hu xs (perform ar .mul a b) 1 (a*b) |a*b|
      (by omega) (abs_nonneg _) le_rfl herr (by simpa [List.length_cons, Nat.add_comm] using hn) hr
    simpa [sequentialDot, List.map_cons, List.sum_cons, List.length_cons, Nat.add_comm] using h

private lemma sum_lower {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hf : ∀ j, i < j → f j = 0) :
    (∑ j, f j) = f i + ∑ j ∈ Finset.Iio i, f j := by
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i)]
  congr 1
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_Iio] at hj
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
    exact ne_of_lt hj
  · intro j hj hji
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hj
    simp only [Finset.mem_Iio] at hji
    exact hf j (lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm hj))

private lemma prefix_sum {n : ℕ} (i : Fin n) (f : Fin n → ℝ) :
    ((((List.finRange n).filter (fun j => j < i)).map f).sum) = ∑ j ∈ Finset.Iio i, f j := by
  rw [← List.sum_toFinset f ((List.nodup_finRange n).filter _)]
  congr 1
  ext j
  simp

private lemma prefix_length {n : ℕ} (i : Fin n) :
    ((List.finRange n).filter (fun j => j < i)).length = i.val := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  have he : ((List.finRange n).filter (fun j => j < i)).toFinset = Finset.Iio i := by
    ext j
    simp
  rw [he, Fin.card_Iio]

private def RowBound {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (b x : Fin n → ℝ) (u : ℝ) (i : Fin n) : Prop :=
  |b i - ∑ j, T i j*x j| ≤ TriangularSolveBounds.g n u * ∑ j, |T i j*x j|

private lemma forwardRow_error {n : ℕ} (ar : Arithmetic) (T : Matrix (Fin n) (Fin n) ℝ)
    (b x y : Fin n → ℝ) (u : ℝ) (i : Fin n) (hu : 0 ≤ u)
    (hn : (n:ℝ)*u < 1) (ht : IsTriangular .lower T) (hd : T i i ≠ 0)
    (hr : (forwardRow ar T b x i).SatisfiesModel ar u)
    (hyi : y i = (forwardRow ar T b x i).value) (hy : ∀ j, j < i → y j = x j) :
    RowBound T b y u i := by
  have hn1 : 1 ≤ n := by have := i.isLt; omega
  have hu1 : u < 1 := by
    have := mul_le_mul_of_nonneg_right (by exact_mod_cast hn1 : (1:ℝ) ≤ n) hu
    nlinarith
  have hs : (∑ j, T i j*y j) = T i i*y i + ∑ j ∈ Finset.Iio i, T i j*x j := by
    rw [sum_lower i _ (fun j hj => by simp [ht i j hj])]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hy j (Finset.mem_Iio.mp hj)]
  have hA : (∑ j, |T i j*y j|) = |T i i*y i| + ∑ j ∈ Finset.Iio i, |T i j*x j| := by
    rw [sum_lower i _ (fun j hj => by simp [ht i j hj])]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hy j (Finset.mem_Iio.mp hj)]
  unfold RowBound
  rw [hs,hA]
  by_cases hi : i.val = 0
  · have hi0 : Finset.Iio i = ∅ := by ext j; simp; omega
    simp only [hi0, Finset.sum_empty, add_zero]
    have hr' : (⟨.div,b i,T i i⟩ : Call).SatisfiesModel ar u := by
      apply hr
      simp [forwardRow,hi,perform]
    obtain ⟨δ,hδ,eδ⟩ : ∃ δ : ℝ, |δ| ≤ u ∧ ar.div (b i) (T i i) = (b i)/(T i i)*(1+δ) := by
      exact hr' (fun _ => hd)
    have hδp : 0 < 1+δ := by have := abs_le.mp hδ; linarith
    have hy' : y i = (b i)/(T i i)*(1+δ) := by simpa [forwardRow,hi,perform,Call.computed,eδ] using hyi
    have heq : b i = (T i i*y i)*(1+δ)⁻¹ := by rw [hy']; field_simp [hd,hδp]
    have herr := TriangularSolveBounds.inverse_error hu hu1 hδ
    have hgn := TriangularSolveBounds.g_mono hu hn1 hn
    calc
      |b i-T i i*y i| = |T i i*y i| *|(1+δ)⁻¹-1| := by rw [heq, ← abs_mul]; congr 1; ring
      _ ≤ |T i i*y i| *TriangularSolveBounds.g n u := mul_le_mul_of_nonneg_left (herr.trans hgn) (abs_nonneg _)
      _ = _ := mul_comm _ _
  · let xs := ((List.finRange n).filter (fun j => j < i)).map (fun j => (T i j,x j))
    let p := sequentialDot ar xs
    let s := ar.sub (b i) p.value
    have hp : p.SatisfiesModel ar u := by
      intro c hc
      apply hr
      simp only [forwardRow,hi, ↓reduceIte, List.mem_append]
      exact Or.inl (Or.inl hc)
    have hrs : (⟨.sub,b i,p.value⟩ : Call).SatisfiesModel ar u := by
      apply hr
      simp [forwardRow,hi,p,xs,perform]
    have hrq : (⟨.div,s,T i i⟩ : Call).SatisfiesModel ar u := by
      apply hr
      simp [forwardRow,hi,p,xs,s,perform,Call.computed]
    obtain ⟨δ,hδ,eδ⟩ : ∃ δ : ℝ, |δ| ≤ u ∧ s = (b i-p.value)*(1+δ) := by
      simpa [Call.SatisfiesModel,Call.computed,Call.exact,s] using hrs
    obtain ⟨ε,hε,eε⟩ : ∃ ε : ℝ, |ε| ≤ u ∧ ar.div s (T i i) = s/(T i i)*(1+ε) := hrq (fun _ => hd)
    have hδp : 1+δ ≠ 0 := by have := abs_le.mp hδ; linarith
    have hεp : 1+ε ≠ 0 := by have := abs_le.mp hε; linarith
    have hy' : y i = s/(T i i)*(1+ε) := by
      simpa [forwardRow,hi,p,xs,s,perform,Call.computed,eε] using hyi
    have heq : b i = p.value+(T i i*y i)*((1+δ)*(1+ε))⁻¹ := by
      rw [hy',eδ]
      field_simp [hd,hδp,hεp]; ring
    have hn2 : 2 ≤ n := by have := i.isLt; omega
    have hu2 : 2*u < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hn2) hu) hn
    have hin : i.val ≤ n := by have := i.isLt; omega
    have hilen : xs.length = i.val := by simp [xs,prefix_length]
    have hdot := sequentialDot_error ar u hu xs (by rw [hilen]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hin) hu) hn) hp
    have hdot' : |p.value - ∑ j ∈ Finset.Iio i, T i j*x j| ≤
        TriangularSolveBounds.g n u * ∑ j ∈ Finset.Iio i, |T i j*x j| := by
      have hd' : |p.value - ∑ j ∈ Finset.Iio i, T i j*x j| ≤ TriangularSolveBounds.g i.val u * ∑ j ∈ Finset.Iio i, |T i j*x j| := by
        simpa [p,xs,List.map_map,Function.comp_def,prefix_sum,hilen,prefix_length] using hdot
      exact hd'.trans (mul_le_mul_of_nonneg_right (TriangularSolveBounds.g_mono hu hin hn) (Finset.sum_nonneg (by intros; positivity)))
    have hinv := (TriangularSolveBounds.inverse_two_error hu hu2 hδ hε).trans (TriangularSolveBounds.g_mono hu hn2 hn)
    calc
      |b i-(T i i*y i+∑ j ∈ Finset.Iio i, T i j*x j)| =
          |(p.value-∑ j ∈ Finset.Iio i, T i j*x j)+(T i i*y i)*(((1+δ)*(1+ε))⁻¹-1)| := by rw [heq]; congr 1; ring
      _ ≤ |p.value-∑ j ∈ Finset.Iio i, T i j*x j|+|T i i*y i| *|((1+δ)*(1+ε))⁻¹-1| := by simpa [abs_mul] using abs_add_le (p.value-∑ j ∈ Finset.Iio i, T i j*x j) ((T i i*y i)*(((1+δ)*(1+ε))⁻¹-1))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hinv (abs_nonneg (T i i*y i))]

private lemma fold_calls {n : ℕ} (ar : Arithmetic) (T : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (xs : List (Fin n)) (state : Execution (Fin n → ℝ)) :
    ∀ c ∈ state.calls, c ∈ (xs.foldl (forwardStep ar T b) state).calls := by
  induction xs generalizing state with
  | nil => simp
  | cons i xs ih =>
    intro c hc
    apply ih
    simp only [forwardStep, List.mem_append]
    exact Or.inl hc

private lemma fold_unchanged {n : ℕ} (ar : Arithmetic) (T : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (xs : List (Fin n)) (state : Execution (Fin n → ℝ))
    (j : Fin n) (hj : j ∉ xs) :
    (xs.foldl (forwardStep ar T b) state).value j = state.value j := by
  induction xs generalizing state with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.mem_cons, not_or] at hj
    rw [List.foldl_cons, ih _ hj.2]
    simp [forwardStep,Function.update_of_ne hj.1]

private lemma rowBound_congr {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (b x y : Fin n → ℝ) (u : ℝ) (i : Fin n) (ht : IsTriangular .lower T)
    (hxy : ∀ j, j ≤ i → x j = y j) (hx : RowBound T b x u i) : RowBound T b y u i := by
  have he : ∀ j, T i j*x j = T i j*y j := by
    intro j
    by_cases h : j ≤ i
    · rw [hxy j h]
    · simp [ht i j (lt_of_not_ge h)]
  simpa only [RowBound,he] using hx

private lemma fold_rows {n : ℕ} (ar : Arithmetic) (T : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (u : ℝ) (hu : 0 ≤ u) (hn : (n:ℝ)*u < 1)
    (ht : IsTriangular .lower T) (hd : ∀ i, T i i ≠ 0)
    (xs : List (Fin n)) (state : Execution (Fin n → ℝ))
    (hsort : xs.Pairwise (· < ·))
    (hr : (xs.foldl (forwardStep ar T b) state).SatisfiesModel ar u) :
    ∀ i ∈ xs, RowBound T b (xs.foldl (forwardStep ar T b) state).value u i := by
  induction xs generalizing state with
  | nil => simp
  | cons i xs ih =>
    have hsorted := List.pairwise_cons.mp hsort
    intro j hj
    rcases List.mem_cons.mp hj with hji | hj
    · subst j
      let next := forwardStep ar T b state i
      have hrow : (forwardRow ar T b state.value i).SatisfiesModel ar u := by
        intro c hc
        apply hr
        apply fold_calls ar T b xs next
        simp only [next,forwardStep,List.mem_append]
        exact Or.inr hc
      have hb : RowBound T b next.value u i := forwardRow_error ar T b state.value next.value u i hu hn ht (hd i) hrow (by simp [next,forwardStep]) (by intro j hj; simp [next,forwardStep,ne_of_lt hj])
      apply rowBound_congr T b next.value _ u i ht _ hb
      intro j hj
      symm
      change (xs.foldl (forwardStep ar T b) next).value j = next.value j
      apply fold_unchanged
      intro hmem
      have := hsorted.1 j hmem
      exact (not_lt_of_ge hj) this
    · exact ih (forwardStep ar T b state i) hsorted.2 hr j hj

private lemma lower_pivots {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (ht : IsTriangular .lower T) (hd : T.det ≠ 0) : ∀ i, T i i ≠ 0 := by
  have hblock : T.BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact ht i j hij
  rw [Matrix.det_of_lowerTriangular T hblock] at hd
  exact fun i => (Finset.prod_ne_zero_iff.mp hd) i (Finset.mem_univ i)

private lemma forward_bounds {n : ℕ} (ar : Arithmetic) (T : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (u : ℝ) (hu : 0 ≤ u) (hn : (n:ℝ)*u < 1)
    (ht : IsTriangular .lower T) (hd : T.det ≠ 0)
    (hr : (forwardSubstitution ar T b).SatisfiesModel ar u) :
    ∀ i, RowBound T b (forwardSubstitution ar T b).value u i := by
  exact fun i => fold_rows ar T b u hu hn ht (lower_pivots T ht hd)
    (List.finRange n) ⟨fun _ => 0,[]⟩ (List.pairwise_lt_finRange n) hr i (List.mem_finRange i)

private lemma perturb_of_residual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a x : ι → ℝ) (c g : ℝ) (hg : 0 ≤ g)
    (hr : |c-∑ j, a j*x j| ≤ g*∑ j, |a j*x j|) :
    ∃ d : ι → ℝ, (∑ j, (a j+d j)*x j) = c ∧
      (∀ j, |d j| ≤ g*|a j|) ∧ (∀ j, a j=0 → d j=0) := by
  let A := ∑ j, |a j*x j|
  let r := c-∑ j, a j*x j
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  by_cases hzero : A = 0
  · have hr0 : r = 0 := by
      have hr' : |r| ≤ g*A := hr
      have : |r| ≤ 0 := by simpa only [hzero,mul_zero] using hr'
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
    refine ⟨fun _ => 0,?_,?_,by simp⟩
    · simpa [r] using (sub_eq_zero.mp hr0).symm
    · intro j
      simp only [abs_zero]
      positivity
  · let d : ι → ℝ := fun j => r/A*|a j| *(if 0 ≤ x j then (1:ℝ) else -1)
    have hratio : |r/A| ≤ g := by
      rw [abs_div,abs_of_pos (lt_of_le_of_ne hA (Ne.symm hzero))]
      exact (div_le_iff₀ (lt_of_le_of_ne hA (Ne.symm hzero))).2 hr
    have hd : ∀ j, d j*x j = r/A*|a j*x j| := by
      intro j
      dsimp [d]
      by_cases hx : 0 ≤ x j
      · simp [hx,abs_mul,abs_of_nonneg hx]; ring
      · simp [hx,abs_mul,abs_of_neg (lt_of_not_ge hx)]; ring
    refine ⟨d,?_,?_,?_⟩
    · simp_rw [add_mul,hd]
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      change (∑ j, a j*x j)+r/A*A = c
      rw [div_mul_cancel₀ _ hzero]
      dsimp [r]
      ring
    · intro j
      dsimp [d]
      rw [abs_mul,abs_mul,abs_abs]
      have hsign : |(if 0 ≤ x j then (1:ℝ) else -1)| ≤ 1 := by
        split_ifs <;> norm_num
      calc
        |r/A| *|a j| *|(if 0 ≤ x j then (1:ℝ) else -1)| ≤ |r/A| *|a j| *1 := mul_le_mul_of_nonneg_left hsign (by positivity)
        _ ≤ g*|a j| := by simpa using mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
    · intro j hj
      simp [d,hj]

private lemma lower_solution {n : ℕ} (ar : Arithmetic) (T : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (u : ℝ) (hu : 0 ≤ u) (hn : (n:ℝ)*u < 1)
    (ht : IsTriangular .lower T) (hd : T.det ≠ 0)
    (hr : (forwardSubstitution ar T b).SatisfiesModel ar u) :
    ∃ Δ : Matrix (Fin n) (Fin n) ℝ,
      (T+Δ).mulVec (forwardSubstitution ar T b).value = b ∧
      (∀ i j, |Δ i j| ≤ gamma n u*|T i j|) ∧ IsTriangular .lower Δ := by
  have hb := forward_bounds ar T b u hu hn ht hd hr
  have hw : ∀ i, ∃ d : Fin n → ℝ,
      (∑ j, (T i j+d j)*(forwardSubstitution ar T b).value j) = b i ∧
      (∀ j, |d j| ≤ TriangularSolveBounds.g n u*|T i j|) ∧
      (∀ j, T i j=0 → d j=0) := by
    intro i
    exact perturb_of_residual (T i) (forwardSubstitution ar T b).value (b i)
      (TriangularSolveBounds.g n u) (TriangularSolveBounds.g_nonneg hu hn) (hb i)
  choose Δ hΔ using hw
  refine ⟨Δ,?_,?_,?_⟩
  · funext i
    exact (hΔ i).1
  · intro i j
    exact (hΔ i).2.1 j
  · intro i j hij
    exact (hΔ i).2.2 j (ht i j hij)

private lemma reverseMatrix_det {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) :
    (reverseMatrix T).det = T.det := by
  exact Matrix.det_submatrix_equiv_self (⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩ : Fin n ≃ Fin n) T

private lemma reverse_sum {n : ℕ} (f : Fin n → ℝ) :
    (∑ i : Fin n, f i.rev) = ∑ i, f i := by
  exact Equiv.sum_comp (⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩ : Fin n ≃ Fin n) f

/-- Solution of a Triangular System (both orientations, arbitrary dimension).
The vector in the perturbed equation is the output of the constructed algorithm
on the original T and b. Nonsingularity is the determinant condition; all
rounding assumptions are elementary-operation laws on its actual trace. -/
theorem solution_of_a_triangular_system
    (n : ℕ) (direction : Direction) (ar : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hnu : (n : ℝ) * u < 1)
    (hnonsingular : T.det ≠ 0) (htriangular : IsTriangular direction T)
    (hround : (substitution direction ar T b).SatisfiesModel ar u) :
    ∃ Δ : Matrix (Fin n) (Fin n) ℝ,
      (T + Δ).mulVec (substitution direction ar T b).value = b ∧
      (∀ i j, |Δ i j| ≤ gamma n u * |T i j|) ∧
      IsTriangular direction Δ := by
  cases direction with
  | lower => exact lower_solution ar T b u hu hnu htriangular hnonsingular hround
  | upper =>
    have ht : IsTriangular .lower (reverseMatrix T) := by
      intro i j hij
      exact htriangular i.rev j.rev (Fin.rev_lt_rev.mpr hij)
    obtain ⟨D,hD,hbound,htri⟩ := lower_solution ar (reverseMatrix T) (reverseVector b) u
      hu hnu ht (by rwa [reverseMatrix_det]) hround
    refine ⟨reverseMatrix D,?_,?_,?_⟩
    · funext i
      have he := congrFun hD i.rev
      change (∑ j, (T i j+D i.rev j.rev)*(forwardSubstitution ar (reverseMatrix T) (reverseVector b)).value j.rev) = b i
      change (∑ j, (T i.rev.rev j.rev+D i.rev j)*(forwardSubstitution ar (reverseMatrix T) (reverseVector b)).value j) = b i.rev.rev at he
      simp only [Fin.rev_rev] at he
      rw [← reverse_sum (fun j => (T i j+D i.rev j.rev)*(forwardSubstitution ar (reverseMatrix T) (reverseVector b)).value j.rev)]
      simpa only [Fin.rev_rev] using he
    · intro i j
      simpa only [reverseMatrix,Fin.rev_rev] using hbound i.rev j.rev
    · intro i j hij
      exact htri i.rev j.rev (Fin.rev_lt_rev.mpr hij)


end TriangularSolve
