import Mathlib

/-!
Formal statement of `theorem:solution_of_a_traingular_system` in the supplied
source. Arithmetic is specified only at operations actually executed; its
relative-error witnesses express the standard model in the absence of overflow
and underflow. No backward-error certificate is an input to the theorem.
-/

namespace Research.TriangularSolve

noncomputable section

/-- The two substitution orders. -/
inductive Direction where
  | lower
  | upper
  deriving DecidableEq

/-- Raw arithmetic operations, before imposing the floating-point model. -/
structure Arithmetic where
  mul : ℝ → ℝ → ℝ
  add : ℝ → ℝ → ℝ
  sub : ℝ → ℝ → ℝ
  div : ℝ → ℝ → ℝ

/-- Standard relative rounding model for one executed operation. -/
def RelativeRound (u exact computed : ℝ) : Prop :=
  ∃ δ : ℝ, |δ| ≤ u ∧ computed = exact * (1 + δ)

/-- The constant in the source, including its value for dimension zero. -/
def gamma (n : ℕ) (u : ℝ) : ℝ :=
  (n : ℝ) * u / (1 - (n : ℝ) * u)

/-- Triangular structure, with the same orientation used by substitution. -/
def Triangular {n : ℕ} (direction : Direction)
    (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  match direction with
  | .lower => ∀ i j, i < j → T i j = 0
  | .upper => ∀ i j, j < i → T i j = 0

/-- Increasing row order for forward substitution and decreasing for backward. -/
def rowOrder (direction : Direction) (n : ℕ) : List (Fin n) :=
  match direction with
  | .lower => List.finRange n
  | .upper => (List.finRange n).reverse

/-- Previously solved columns, in the same order as the row traversal. -/
def previousColumns {n : ℕ} (direction : Direction) (i : Fin n) : List (Fin n) :=
  (rowOrder direction n).filter fun j =>
    match direction with
    | .lower => j < i
    | .upper => i < j

/-- Continue a sequential dot product from its current accumulator. -/
def dotAcc {n : ℕ} (ops : Arithmetic) (a x : Fin n → ℝ) :
    List (Fin n) → ℝ → ℝ
  | [], acc => acc
  | j :: js, acc => dotAcc ops a x js (ops.add acc (ops.mul (a j) (x j)))

/-- Sequential dot product: the first product seeds the accumulator, so there
is no extra addition of zero. The empty product needs no rounded operation. -/
def roundedDot {n : ℕ} (ops : Arithmetic) (a x : Fin n → ℝ) :
    List (Fin n) → ℝ
  | [] => 0
  | j :: js => dotAcc ops a x js (ops.mul (a j) (x j))

/-- Legal rounding at all remaining dot-product operations. -/
def DotAccValid {n : ℕ} (u : ℝ) (ops : Arithmetic) (a x : Fin n → ℝ) :
    List (Fin n) → ℝ → Prop
  | [], _ => True
  | j :: js, acc =>
      RelativeRound u (a j * x j) (ops.mul (a j) (x j)) ∧
      RelativeRound u (acc + ops.mul (a j) (x j))
        (ops.add acc (ops.mul (a j) (x j))) ∧
      DotAccValid u ops a x js (ops.add acc (ops.mul (a j) (x j)))

/-- Legal rounding at precisely the operations of `roundedDot`. -/
def DotValid {n : ℕ} (u : ℝ) (ops : Arithmetic) (a x : Fin n → ℝ) :
    List (Fin n) → Prop
  | [] => True
  | j :: js =>
      RelativeRound u (a j * x j) (ops.mul (a j) (x j)) ∧
      DotAccValid u ops a x js (ops.mul (a j) (x j))

/-- Numerator for a row solve. The first solved row uses b directly. -/
def rowNumerator {n : ℕ} (direction : Direction) (ops : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) (i : Fin n) : ℝ :=
  match previousColumns direction i with
  | [] => b i
  | js@(_ :: _) => ops.sub (b i) (roundedDot ops (T i) x js)

/-- Execute one row and replace the corresponding component of the state. -/
def solveRow {n : ℕ} (direction : Direction) (ops : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) (i : Fin n) : Fin n → ℝ :=
  Function.update x i (ops.div (rowNumerator direction ops T b x i) (T i i))

/-- The no-overflow/no-underflow standard model at this row's executed calls.
Nonzero pivots are a consequence of triangularity and nonsingularity, rather
than an additional assumption here. -/
def RowValid {n : ℕ} (u : ℝ) (direction : Direction) (ops : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) (i : Fin n) : Prop :=
  DotValid u ops (T i) x (previousColumns direction i) ∧
  (match previousColumns direction i with
   | [] => True
   | js@(_ :: _) =>
       RelativeRound u (b i - roundedDot ops (T i) x js)
         (ops.sub (b i) (roundedDot ops (T i) x js))) ∧
  RelativeRound u (rowNumerator direction ops T b x i / T i i)
    (ops.div (rowNumerator direction ops T b x i) (T i i))

/-- Substitution as a concrete finite state traversal. -/
def solveRows {n : ℕ} (direction : Direction) (ops : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    List (Fin n) → (Fin n → ℝ) → (Fin n → ℝ)
  | [], x => x
  | i :: is, x => solveRows direction ops T b is (solveRow direction ops T b x i)

/-- Standard model at every operation on the actual substitution execution. -/
def RowsValid {n : ℕ} (u : ℝ) (direction : Direction) (ops : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    List (Fin n) → (Fin n → ℝ) → Prop
  | [], _ => True
  | i :: is, x =>
      RowValid u direction ops T b x i ∧
      RowsValid u direction ops T b is (solveRow direction ops T b x i)

/-- The computed solution on the original T and b. -/
def computedSolution {n : ℕ} (direction : Direction) (ops : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  solveRows direction ops T b (rowOrder direction n) (fun _ => 0)

/-- No overflow or underflow, expressed through the source's relative-error
model at the calls actually made by `computedSolution`. -/
def ExecutionValid {n : ℕ} (u : ℝ) (direction : Direction) (ops : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : Prop :=
  RowsValid u direction ops T b (rowOrder direction n) (fun _ => 0)

/-- A single direct or reciprocal rounding factor. -/
def Factor (u r : ℝ) : Prop :=
  ∃ d : ℝ, |d| ≤ u ∧ (r = 1 + d ∨ r = (1 + d)⁻¹)

/-- A product with an explicit operation count. -/
def Factors (u : ℝ) (k : ℕ) (r : ℝ) : Prop :=
  ∃ l : List ℝ, l.length ≤ k ∧ (∀ t ∈ l, Factor u t) ∧ r = l.prod

lemma factors_one (u : ℝ) (k : ℕ) : Factors u k 1 :=
  ⟨[], Nat.zero_le _, by simp, by simp⟩

lemma factors_mono {u r : ℝ} {k m : ℕ} (h : Factors u k r) (hkm : k ≤ m) :
    Factors u m r := by
  obtain ⟨l, hl, hf, rfl⟩ := h
  exact ⟨l, hl.trans hkm, hf, rfl⟩

lemma factors_mul {u a b : ℝ} {k m : ℕ} (ha : Factors u k a)
    (hb : Factors u m b) : Factors u (k + m) (a * b) := by
  obtain ⟨l, hl, hf, rfl⟩ := ha
  obtain ⟨s, hs, hg, rfl⟩ := hb
  exact ⟨l ++ s, by simpa using Nat.add_le_add hl hs,
    by intro t ht; rcases List.mem_append.mp ht with ht | ht; exact hf t ht; exact hg t ht, by simp⟩

lemma factors_single {u d : ℝ} (hd : |d| ≤ u) : Factors u 1 (1 + d) :=
  ⟨[1+d], by simp, by simpa using (show Factor u (1+d) from ⟨d, hd, Or.inl rfl⟩), by simp⟩

lemma factors_inv_single {u d : ℝ} (hd : |d| ≤ u) : Factors u 1 ((1 + d)⁻¹) :=
  ⟨[(1+d)⁻¹], by simp,
    by simpa using (show Factor u ((1+d)⁻¹) from ⟨d, hd, Or.inr rfl⟩), by simp⟩

lemma factor_interval {u r : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) (h : Factor u r) :
    1 - u ≤ r ∧ r ≤ (1-u)⁻¹ := by
  obtain ⟨d, hd, h | h⟩ := h <;> subst r
  all_goals obtain ⟨hdlo, hdhi⟩ := abs_le.mp hd
  · constructor
    · linarith
    · rw [inv_eq_one_div]
      apply (le_div_iff₀ (by linarith : 0 < 1-u)).2
      nlinarith [sq_nonneg u]
  · have hp : 0 < 1+d := by linarith
    constructor
    · rw [inv_eq_one_div]
      apply (le_div_iff₀ hp).2
      nlinarith [sq_nonneg u]
    · exact (inv_le_inv₀ hp (by linarith : 0 < 1-u)).2 (by linarith)

lemma product_interval {u : ℝ} (hu : 0 ≤ u) (l : List ℝ)
    (hl : (l.length : ℝ)*u < 1) (hf : ∀ r ∈ l, Factor u r) :
    1 - (l.length : ℝ)*u ≤ l.prod ∧
      l.prod ≤ (1 - (l.length : ℝ)*u)⁻¹ := by
  induction l with
  | nil => simp
  | cons r l ih =>
    have hc : ( (r :: l).length : ℝ) = (l.length : ℝ)+1 := by simp
    rw [hc] at hl ⊢
    have hm : (l.length : ℝ)*u < 1 := by nlinarith
    have hu1 : u < 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) l.length]
    obtain ⟨hlo, hhi⟩ := ih hm (fun t ht => hf t (by simp [ht]))
    obtain ⟨hrlo, hrhi⟩ := factor_interval hu hu1 (hf r (by simp))
    have hp : 0 < 1 - (l.length : ℝ)*u := by linarith
    have hq : 0 < 1-u := by linarith
    have hs : 0 < 1 - ((l.length : ℝ)+1)*u := by linarith
    rw [List.prod_cons]
    constructor
    · calc
        1 - ((l.length : ℝ)+1)*u ≤ (1-u)*(1-(l.length : ℝ)*u) := by
          nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) l.length) (sq_nonneg u)]
        _ ≤ r*l.prod := mul_le_mul hrlo hlo (le_of_lt hp) (by linarith)
    · calc
        r*l.prod ≤ (1-u)⁻¹ * (1-(l.length : ℝ)*u)⁻¹ :=
          mul_le_mul hrhi hhi (by linarith) (inv_nonneg.mpr (le_of_lt hq))
        _ = ((1-u)*(1-(l.length : ℝ)*u))⁻¹ := by rw [mul_inv]
        _ ≤ (1-((l.length : ℝ)+1)*u)⁻¹ := by
          apply (inv_le_inv₀ (mul_pos hq hp) hs).2
          nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) l.length) (sq_nonneg u)]

lemma gamma_mono {u : ℝ} (hu : 0 ≤ u) {k n : ℕ} (hkn : k ≤ n)
    (hn : (n : ℝ)*u < 1) : gamma k u ≤ gamma n u := by
  have hku : (k : ℝ)*u ≤ (n : ℝ)*u := mul_le_mul_of_nonneg_right (by exact_mod_cast hkn) hu
  unfold gamma
  apply (div_le_div_iff₀ (by linarith : 0 < 1-(k:ℝ)*u) (by linarith : 0 < 1-(n:ℝ)*u)).2
  nlinarith

lemma factors_bound {u r : ℝ} {k : ℕ} (hu : 0 ≤ u) (hk : (k:ℝ)*u < 1)
    (h : Factors u k r) : |r-1| ≤ gamma k u := by
  obtain ⟨l, hl, hf, rfl⟩ := h
  have hle : (l.length:ℝ)*u ≤ (k:ℝ)*u :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hu
  obtain ⟨hlo,hhi⟩ := product_interval hu l (by linarith) hf
  have hp : 0 < 1-(l.length:ℝ)*u := by linarith
  have hnonneg : 0 ≤ (l.length:ℝ)*u := mul_nonneg (Nat.cast_nonneg _) hu
  have hb : |l.prod-1| ≤ gamma l.length u := by
    apply abs_le.mpr
    unfold gamma
    constructor
    · have hh : (l.length:ℝ)*u ≤ (l.length:ℝ)*u / (1-(l.length:ℝ)*u) := by
        apply (le_div_iff₀ hp).2
        nlinarith [sq_nonneg ((l.length:ℝ)*u)]
      linarith
    · have he : (1-(l.length:ℝ)*u)⁻¹ - 1 =
          (l.length:ℝ)*u / (1-(l.length:ℝ)*u) := by field_simp; ring
      linarith
  exact hb.trans (gamma_mono hu hl hk)

lemma dotAcc_expansion {n : ℕ} (u : ℝ) (ops : Arithmetic) (a x : Fin n → ℝ)
    (js : List (Fin n)) (acc : ℝ) (hnd : js.Nodup)
    (hv : DotAccValid u ops a x js acc) :
    ∃ q : ℝ, ∃ r : Fin n → ℝ,
      Factors u js.length q ∧
      (∀ j ∈ js, Factors u (js.length + 1) (r j)) ∧
      dotAcc ops a x js acc = acc*q + (js.map (fun j => a j*x j*r j)).sum := by
  induction js generalizing acc with
  | nil => exact ⟨1, fun _ => 1, factors_one _ _, by simp, by simp [dotAcc]⟩
  | cons j js ih =>
    obtain ⟨hm, ha, ht⟩ := hv
    obtain ⟨dm, hdm, em⟩ := hm
    obtain ⟨da, hda, ea⟩ := ha
    obtain ⟨q, r, hq, hr, he⟩ := ih _ hnd.tail ht
    let q' := (1+da)*q
    let r' := Function.update r j ((1+dm)*q')
    have hq' : Factors u (js.length+1) q' := by
      simpa [q', Nat.add_comm] using factors_mul (factors_single hda) hq
    refine ⟨q', r', hq', ?_, ?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · simpa [r', Nat.add_comm] using factors_mul (factors_single hdm) hq'
      · have hne : t ≠ j := fun h => (List.nodup_cons.mp hnd).1 (h ▸ ht)
        simpa [r', hne] using factors_mono (hr t ht) (Nat.le_succ _)
    · have hs : (js.map (fun t => a t*x t*r' t)).sum =
          (js.map (fun t => a t*x t*r t)).sum := by
        congr 1
        apply List.map_congr_left
        intro t ht
        have hne : t ≠ j := fun h => (List.nodup_cons.mp hnd).1 (h ▸ ht)
        simp [r', hne]
      simp only [dotAcc, List.map_cons, List.sum_cons]
      rw [he, hs, ea, em]
      simp only [r', Function.update_self]
      dsimp [q']
      ring

lemma dot_expansion {n : ℕ} (u : ℝ) (ops : Arithmetic) (a x : Fin n → ℝ)
    (js : List (Fin n)) (hnd : js.Nodup) (hv : DotValid u ops a x js) :
    ∃ r : Fin n → ℝ, (∀ j ∈ js, Factors u js.length (r j)) ∧
      roundedDot ops a x js = (js.map (fun j => a j*x j*r j)).sum := by
  cases js with
  | nil => exact ⟨fun _ => 1, by simp, by simp [roundedDot]⟩
  | cons j js =>
    obtain ⟨hm, ht⟩ := hv
    obtain ⟨dm, hdm, em⟩ := hm
    obtain ⟨q, r, hq, hr, he⟩ := dotAcc_expansion u ops a x js _ hnd.tail ht
    let r' := Function.update r j ((1+dm)*q)
    refine ⟨r', ?_, ?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · simpa [r', Nat.add_comm] using factors_mul (factors_single hdm) hq
      · have hne : t ≠ j := fun h => (List.nodup_cons.mp hnd).1 (h ▸ ht)
        simpa [r', hne] using hr t ht
    · have hs : (js.map (fun t => a t*x t*r' t)).sum =
          (js.map (fun t => a t*x t*r t)).sum := by
        congr 1
        apply List.map_congr_left
        intro t ht
        have hne : t ≠ j := fun h => (List.nodup_cons.mp hnd).1 (h ▸ ht)
        simp [r', hne]
      simp only [roundedDot, List.map_cons, List.sum_cons]
      rw [he, hs, em]
      simp only [r', Function.update_self]
      ring

lemma rowOrder_nodup (direction : Direction) (n : ℕ) : (rowOrder direction n).Nodup := by
  cases direction <;> simp [rowOrder, List.nodup_finRange]

lemma mem_rowOrder {n : ℕ} (direction : Direction) (i : Fin n) :
    i ∈ rowOrder direction n := by
  cases direction <;> simp [rowOrder, List.mem_finRange]

lemma mem_previous {n : ℕ} (direction : Direction) (i j : Fin n) :
    j ∈ previousColumns direction i ↔
      match direction with | .lower => j < i | .upper => i < j := by
  cases direction <;> simp [previousColumns, rowOrder, List.mem_finRange]

lemma previous_nodup {n : ℕ} (direction : Direction) (i : Fin n) :
    (previousColumns direction i).Nodup :=
  (rowOrder_nodup direction n).filter _

lemma self_not_previous {n : ℕ} (direction : Direction) (i : Fin n) :
    i ∉ previousColumns direction i := by
  rw [mem_previous]; cases direction <;> simp

lemma previous_length {n : ℕ} (direction : Direction) (i : Fin n) :
    (previousColumns direction i).length + 1 ≤ n := by
  have h := (List.nodup_cons.mpr ⟨self_not_previous direction i, previous_nodup direction i⟩).length_le_card
  simpa using h

lemma diagonal_nonzero {n : ℕ} (direction : Direction)
    (T : Matrix (Fin n) (Fin n) ℝ) (ht : Triangular direction T) (hd : T.det ≠ 0)
    (i : Fin n) : T i i ≠ 0 := by
  have he : T.det = ∏ j, T j j := by
    cases direction with
    | lower => exact Matrix.det_of_lowerTriangular T (by simpa [Matrix.BlockTriangular, Triangular] using ht)
    | upper => exact Matrix.det_of_upperTriangular (by simpa [Matrix.BlockTriangular, Triangular] using ht)
  rw [he] at hd
  exact (Finset.prod_ne_zero_iff.mp hd) i (Finset.mem_univ _)

lemma local_row {n : ℕ} (direction : Direction) (ops : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) (u : ℝ) (i : Fin n)
    (hu : 0 ≤ u) (hn : (n:ℝ)*u < 1) (hpivot : T i i ≠ 0)
    (hv : RowValid u direction ops T b x i) :
    ∃ r : Fin n → ℝ,
      (∀ j, j = i ∨ j ∈ previousColumns direction i → |r j-1| ≤ gamma n u) ∧
      T i i * (solveRow direction ops T b x i i) * r i +
        ((previousColumns direction i).map (fun j => T i j*x j*r j)).sum = b i := by
  have hlen := previous_length direction i
  have hnd := previous_nodup direction i
  have hnot := self_not_previous direction i
  obtain ⟨hdot, hsub, hdiv⟩ := hv
  have hu1 : u < 1 := by
    have hi : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n from by omega)
    nlinarith
  obtain ⟨dd, hdd, ed⟩ := hdiv
  have hdd0 : 1+dd ≠ 0 := by have := (abs_le.mp hdd).1; linarith
  have hy : solveRow direction ops T b x i i =
      (rowNumerator direction ops T b x i / T i i) * (1+dd) := by
    simpa [solveRow] using ed
  cases hj : previousColumns direction i with
  | nil =>
    refine ⟨fun _ => (1+dd)⁻¹, ?_, ?_⟩
    · intro j _
      exact factors_bound hu hn (factors_mono (factors_inv_single hdd) (by omega))
    · simp only [hj, List.map_nil, List.sum_nil, add_zero]
      rw [hy]
      simp only [rowNumerator, hj]
      field_simp
  | cons j js =>
    rw [hj] at hdot hsub hlen hnd hnot
    obtain ⟨r, hr, er⟩ := dot_expansion u ops (T i) x (j::js) hnd hdot
    obtain ⟨ds, hds, es⟩ := hsub
    have hds0 : 1+ds ≠ 0 := by have := (abs_le.mp hds).1; linarith
    let ri := (1+ds)⁻¹ * (1+dd)⁻¹
    let r' := Function.update r i ri
    have hri : Factors u 2 ri := factors_mul (factors_inv_single hds) (factors_inv_single hdd)
    refine ⟨r', ?_, ?_⟩
    · intro t ht
      rcases ht with rfl | ht
      · simp only [r', Function.update_self]
        exact factors_bound hu hn (factors_mono hri (by simp at hlen; omega))
      · have hne : t ≠ i := fun he => hnot (he ▸ ht)
        simp only [r', Function.update_of_ne hne]
        exact factors_bound hu hn (factors_mono (hr t ht) (by omega))
    · have hs : ((j::js).map (fun t => T i t*x t*r' t)).sum =
          ((j::js).map (fun t => T i t*x t*r t)).sum := by
        congr 1
        apply List.map_congr_left
        intro t ht
        have hne : t ≠ i := fun he => hnot (he ▸ ht)
        simp [r', hne]
      rw [hs, ← er, hy]
      simp only [r', Function.update_self, rowNumerator, hj]
      rw [es]
      dsimp [ri]
      field_simp
      <;> ring

lemma previous_asymm {n : ℕ} (direction : Direction) (i j : Fin n)
    (h : i ∈ previousColumns direction j) : j ∉ previousColumns direction i := by
  rw [mem_previous] at h ⊢
  cases direction <;> exact not_lt_of_gt h

lemma rowOrder_pairwise (direction : Direction) (n : ℕ) :
    (rowOrder direction n).Pairwise (fun i j => i ∈ previousColumns direction j) := by
  cases direction with
  | lower => simpa only [rowOrder, mem_previous] using List.pairwise_lt_finRange n
  | upper =>
    rw [rowOrder, List.pairwise_reverse]
    simpa only [mem_previous] using List.pairwise_lt_finRange n

lemma solveRows_unchanged {n : ℕ} (direction : Direction) (ops : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (is : List (Fin n)) (x : Fin n → ℝ) (j : Fin n) (hj : j ∉ is) :
    solveRows direction ops T b is x j = x j := by
  induction is generalizing x with
  | nil => rfl
  | cons i is ih =>
    rw [List.mem_cons, not_or] at hj
    rw [solveRows, ih _ hj.2]
    exact Function.update_of_ne hj.1 _ _

lemma row_witness {n : ℕ} (direction : Direction) (ops : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (u : ℝ)
    (is : List (Fin n)) (x : Fin n → ℝ)
    (horder : is.Pairwise (fun i j => i ∈ previousColumns direction j))
    (hv : RowsValid u direction ops T b is x) (i : Fin n) (hi : i ∈ is) :
    ∃ z : Fin n → ℝ, RowValid u direction ops T b z i ∧
      solveRows direction ops T b is x i = solveRow direction ops T b z i i ∧
      ∀ j ∈ previousColumns direction i, solveRows direction ops T b is x j = z j := by
  induction is generalizing x with
  | nil => simp at hi
  | cons t is ih =>
    obtain ⟨ht, htail⟩ := List.pairwise_cons.mp horder
    obtain ⟨hvrow, hvrest⟩ := hv
    rcases List.mem_cons.mp hi with rfl | hi
    · refine ⟨x, hvrow, ?_, ?_⟩
      · rw [solveRows]
        apply solveRows_unchanged
        intro hm
        exact self_not_previous direction i (ht i hm)
      · intro j hj
        rw [solveRows, solveRows_unchanged]
        · exact Function.update_of_ne (show j ≠ i from fun he => self_not_previous direction i (he ▸ hj)) _ _
        · intro hm
          exact previous_asymm direction j i hj (ht j hm)
    · exact ih _ htail hvrest hi

lemma final_row {n : ℕ} (direction : Direction) (ops : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hn : (n:ℝ)*u < 1) (ht : Triangular direction T)
    (hd : T.det ≠ 0) (hv : ExecutionValid u direction ops T b) (i : Fin n) :
    ∃ r : Fin n → ℝ,
      (∀ j, j = i ∨ j ∈ previousColumns direction i → |r j-1| ≤ gamma n u) ∧
      T i i * (computedSolution direction ops T b i) * r i +
        ((previousColumns direction i).map
          (fun j => T i j * computedSolution direction ops T b j * r j)).sum = b i := by
  obtain ⟨z, hz, hi, hj⟩ := row_witness direction ops T b u (rowOrder direction n)
    (fun _ => 0) (rowOrder_pairwise direction n) hv i (mem_rowOrder direction i)
  obtain ⟨r, hr, he⟩ := local_row direction ops T b z u i hu hn
    (diagonal_nonzero direction T ht hd i) hz
  refine ⟨r, hr, ?_⟩
  change computedSolution direction ops T b i = _ at hi
  change ∀ j ∈ previousColumns direction i, computedSolution direction ops T b j = z j at hj
  rw [hi]
  have hs : ((previousColumns direction i).map
          (fun j => T i j * computedSolution direction ops T b j * r j)).sum =
      ((previousColumns direction i).map (fun j => T i j*z j*r j)).sum := by
    congr 1
    apply List.map_congr_left
    intro j hmem
    rw [hj j hmem]
  rw [hs]
  exact he

lemma triangle_zero {n : ℕ} (direction : Direction) (T : Matrix (Fin n) (Fin n) ℝ)
    (ht : Triangular direction T) (i j : Fin n) (hne : j ≠ i)
    (hj : j ∉ previousColumns direction i) : T i j = 0 := by
  rw [mem_previous] at hj
  cases direction with
  | lower => exact ht i j (lt_of_le_of_ne (not_lt.mp hj) (Ne.symm hne))
  | upper => exact ht i j (lt_of_le_of_ne (not_lt.mp hj) hne)

lemma sum_active {n : ℕ} (direction : Direction) (i : Fin n) (c : Fin n → ℝ)
    (hc : ∀ j, j ≠ i → j ∉ previousColumns direction i → c j = 0) :
    ∑ j, c j = c i + ((previousColumns direction i).map c).sum := by
  have hn : (i :: previousColumns direction i).Nodup :=
    List.nodup_cons.mpr ⟨self_not_previous direction i, previous_nodup direction i⟩
  calc
    ∑ j, c j = ∑ j ∈ (i :: previousColumns direction i).toFinset, c j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp only [List.mem_toFinset, List.mem_cons, not_or] at hj
      exact hc j hj.1 hj.2
    _ = c i + ((previousColumns direction i).map c).sum := by
      rw [List.sum_toFinset c hn]
      rfl

/-- Solution of a Triangular System (the full selected source statement).
`T.det ≠ 0` is nonsingularity over ℝ. Both orientations and dimension zero
are included; the latter executes no arithmetic. The perturbation has the
same triangular structure and a componentwise relative bound with gamma_n.
Only the proof is left for the next role; all computations above have bodies. -/
theorem solution_of_a_triangular_system
    {n : ℕ} (direction : Direction) (ops : Arithmetic)
    (T : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (u : ℝ)
    (hu : 0 ≤ u)
    (htriangular : Triangular direction T)
    (hnonsingular : T.det ≠ 0)
    (hsize : (n : ℝ) * u < 1)
    (hexecution : ExecutionValid u direction ops T b) :
    ∃ ΔT : Matrix (Fin n) (Fin n) ℝ,
      (T + ΔT).mulVec (computedSolution direction ops T b) = b ∧
      Triangular direction ΔT ∧
      ∀ i j, |ΔT i j| ≤ gamma n u * |T i j| := by
  classical
  choose r hr he using final_row direction ops T b u hu hsize htriangular hnonsingular hexecution
  let Δ : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    T i j * (if j = i ∨ j ∈ previousColumns direction i then r i j - 1 else 0)
  have hg : 0 ≤ gamma n u :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg n) hu) (by linarith)
  refine ⟨Δ, ?_, ?_, ?_⟩
  · funext i
    change ∑ j, (T i j + Δ i j) * computedSolution direction ops T b j = b i
    have hent (j : Fin n) :
        (T i j + Δ i j) * computedSolution direction ops T b j =
        T i j * computedSolution direction ops T b j * r i j := by
      by_cases hj : j = i ∨ j ∈ previousColumns direction i
      · simp only [Δ, if_pos hj]
        ring
      · have hz := triangle_zero direction T htriangular i j (not_or.mp hj).1 (not_or.mp hj).2
        simp [Δ, hz]
    simp_rw [hent]
    rw [sum_active direction i _ (by
      intro j hji hj
      simp [triangle_zero direction T htriangular i j hji hj])]
    exact he i
  · cases direction with
    | lower =>
      intro i j hij
      have hz := htriangular i j hij
      simp [Δ, hz]
    | upper =>
      intro i j hij
      have hz := htriangular i j hij
      simp [Δ, hz]
  · intro i j
    by_cases hj : j = i ∨ j ∈ previousColumns direction i
    · simp only [Δ, if_pos hj, abs_mul]
      calc
        |T i j| * |r i j-1| ≤ |T i j| * gamma n u :=
          mul_le_mul_of_nonneg_left (hr i j hj) (abs_nonneg _)
        _ = gamma n u * |T i j| := mul_comm _ _
    · simpa [Δ, hj] using mul_nonneg hg (abs_nonneg (T i j))

end

end Research.TriangularSolve
