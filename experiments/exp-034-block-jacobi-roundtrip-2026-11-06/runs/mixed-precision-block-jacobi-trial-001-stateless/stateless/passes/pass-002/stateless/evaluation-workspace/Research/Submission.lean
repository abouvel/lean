import Mathlib

/-!
Statement skeleton for the selected theorem in /spec/source.txt.
All arithmetic kernels below have bodies. Only the final mathematical theorem
is left for the proving role. See Research/STATEMENT_NOTES.md for the source
interpretation (successful factorization, square roots, and input conversion).
-/

noncomputable section

namespace MixedPrecisionBlockJacobi

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A separate local relative error at each operation address. -/
abbrev Tape := List ℕ → ℝ

def TapeAdmissible (u : ℝ) (t : Tape) : Prop := ∀ address, |t address| ≤ u

def subTape (p : List ℕ) (t : Tape) : Tape := fun q => t (p ++ q)

/-- The standard real-valued relative-error model; finiteness and absence of
underflow/overflow are represented by this model being valid at every operation. -/
def rounded (t : Tape) (address : List ℕ) (z : ℝ) : ℝ :=
  z * (1 + t address)

/-- Sequential reduction, with no addition to an artificial initial zero. -/
def roundedSum (t : Tape) (ids : List ℕ) (v : ℕ → ℝ) : ℝ :=
  match ids with
  | [] => 0
  | j :: js => js.foldl (fun s k => rounded t [k] (s + v k)) (v j)

/-- Products are rounded individually; the partial sums are reduced sequentially. -/
def roundedDot (t : Tape) (ids : List ℕ) (a b : ℕ → ℝ) : ℝ :=
  roundedSum (subTape [1] t) ids (fun k => rounded t [0, k] (a k * b k))

/-- Zero extension is only used outside the matrix's index range. With S ∣ n
and 0 < S, every tile below is full and these extra entries are never accessed. -/
def entry (v : Vec n) (j : ℕ) : ℝ := if h : j < n then v ⟨j, h⟩ else 0

/-- Two sequential levels of reduction, with S entries per tile. -/
def tiledDot (S : ℕ) (t : Tape) (a b : Vec n) : ℝ :=
  roundedSum (subTape [1] t) (List.range (n / S)) (fun tile =>
    roundedDot (subTape [0, tile] t) (List.range S)
      (fun j => entry a (tile * S + j))
      (fun j => entry b (tile * S + j)))

def tiledMatvec (S : ℕ) (t : Fin n → Tape) (A : Mat n) (v : Vec n) : Vec n :=
  fun i => tiledDot S (t i) (A i) v

/-- The exact block partition, including a possible reordering of coordinates. -/
def blockDiagonal (layout : Fin n ≃ Fin B × Fin T)
    (blocks : Fin B → Mat T) : Mat n :=
  fun i j => if (layout i).1 = (layout j).1 then
    blocks (layout i).1 (layout i).2 (layout j).2 else 0

/-- The Cholesky recurrence uses a rounded dot product followed by subtraction.
For an empty dot product, it uses the input directly (the first-row case). -/
def cholNumerator (t : Tape) (A R : Mat T) (i j : Fin T) : ℝ :=
  if i.val = 0 then A i j else
    rounded t [1] (A i j - roundedDot (subTape [0] t) (List.range i.val)
      (fun k => entry (fun l => R l i) k)
      (fun k => entry (fun l => R l j) k))

/-- Compute one off-diagonal entry of the upper Cholesky factor.
A zero divisor is a failed execution, rather than an extra mathematical hypothesis. -/
def cholOffDiagonal (t : Tape) (A R : Mat T) (i j : Fin T) : Option (Mat T) :=
  if R i i = 0 then none else
    let z := rounded t [2] (cholNumerator t A R i j / R i i)
    some (Function.update R i (Function.update (R i) j z))

/-- Compute a diagonal entry. The rounded square root follows the usual
relative-error model for correctly rounded sqrt, with a fresh local error. -/
def cholDiagonal (t : Tape) (A R : Mat T) (j : Fin T) : Option (Mat T) :=
  let d := cholNumerator t A R j j
  if 0 < d then
    let z := rounded t [2] (Real.sqrt d)
    some (Function.update R j (Function.update (R j) j z))
  else none

/-- Column-oriented upper Cholesky: off-diagonal entries in increasing row
order, then the diagonal. All arrays start at zero. -/
def cholesky (t : Tape) (A : Mat T) : Option (Mat T) :=
  (List.finRange T).foldlM (fun R j => do
    let R' ← ((List.finRange T).filter (fun i => i.val < j.val)).foldlM
      (fun Q i => cholOffDiagonal (subTape [j.val, i.val] t) A Q i j) R
    cholDiagonal (subTape [j.val, j.val] t) A R' j) 0

/-- Actual returned factor; the theorem separately requires a successful run. -/
def computedFactor (t : Tape) (A : Mat T) : Mat T := (cholesky t A).getD 0

/-- One triangular substitution row: dot product, subtraction, division.
An empty row uses only the division, as required by the source's sharp constants. -/
def triangularRow (t : Tape) (ids : List ℕ) (a y : Vec T) (b diagonal : ℝ) : ℝ :=
  let numerator := if ids.isEmpty then b else
    rounded t [1] (b - roundedDot (subTape [0] t) ids (entry a) (entry y))
  rounded t [2] (numerator / diagonal)

/-- Solve Rᵀ y = b in increasing row order. -/
def forwardSubstitution (t : Tape) (R : Mat T) (b : Vec T) : Vec T :=
  (List.finRange T).foldl (fun y i =>
    Function.update y i (triangularRow (subTape [i.val] t) (List.range i.val)
      (fun j => R j i) y (b i) (R i i))) 0

/-- Solve R c = y in decreasing row order. -/
def backwardSubstitution (t : Tape) (R : Mat T) (y : Vec T) : Vec T :=
  (List.finRange T).reverse.foldl (fun c i =>
    Function.update c i (triangularRow (subTape [i.val] t)
      ((List.range T).filter (fun j => i.val < j)) (R i) c (y i) (R i i))) 0

/-- Independent error tapes for factorization and every step of the iteration.
Factorizations are performed once and reused for all correction solves. -/
structure Execution (n B : ℕ) where
  factor : Fin B → Tape
  matvec : ℕ → Fin n → Tape
  residual : ℕ → Fin n → Tape
  conversion : ℕ → Fin n → Tape
  forward : ℕ → Fin B → Tape
  backward : ℕ → Fin B → Tape
  update : ℕ → Fin n → Tape

def Execution.Admissible (E : Execution n B) (us uc : ℝ) : Prop :=
  (∀ l, TapeAdmissible uc (E.factor l)) ∧
  (∀ k i, TapeAdmissible us (E.matvec k i)) ∧
  (∀ k i, TapeAdmissible us (E.residual k i)) ∧
  (∀ k i, TapeAdmissible uc (E.conversion k i)) ∧
  (∀ k l, TapeAdmissible uc (E.forward k l)) ∧
  (∀ k l, TapeAdmissible uc (E.backward k l)) ∧
  (∀ k i, TapeAdmissible us (E.update k i))

def factorBlocks (blocks : Fin B → Mat T) (E : Execution n B) : Fin B → Mat T :=
  fun l => computedFactor (E.factor l) (blocks l)

def computedFactors (layout : Fin n ≃ Fin B × Fin T)
    (blocks : Fin B → Mat T) (E : Execution n B) : Mat n :=
  blockDiagonal layout (factorBlocks blocks E)

def computedResidual (S : ℕ) (E : Execution n B) (A : Mat n)
    (b v : Vec n) (k : ℕ) : Vec n :=
  let z := tiledMatvec S (E.matvec k) A v
  fun i => rounded (E.residual k i) [] (b i - z i)

/-- Conversion of the high-precision residual into the correction precision.
An exact conversion is the admissible special case of zero local error. -/
def convertedResidual (E : Execution n B) (r : Vec n) (k : ℕ) : Vec n :=
  fun i => rounded (E.conversion k i) [] (r i)

def computedCorrection (layout : Fin n ≃ Fin B × Fin T)
    (blocks : Fin B → Mat T) (E : Execution n B) (r : Vec n) (k : ℕ) : Vec n :=
  let rhs := convertedResidual E r k
  let c : Fin B → Vec T := fun l =>
    let R := factorBlocks blocks E l
    let y := forwardSubstitution (E.forward k l) R
      (fun j => rhs (layout.symm (l, j)))
    backwardSubstitution (E.backward k l) R y
  fun i => c (layout i).1 (layout i).2

def jacobiStep (layout : Fin n ≃ Fin B × Fin T) (S : ℕ)
    (blocks : Fin B → Mat T) (E : Execution n B) (A : Mat n)
    (b v : Vec n) (k : ℕ) : Vec n :=
  let r := computedResidual S E A b v k
  let c := computedCorrection layout blocks E r k
  fun i => rounded (E.update k i) [] (v i + c i)

/-- The computed iterates, starting from the given initial vector. -/
def iterates (layout : Fin n ≃ Fin B × Fin T) (S : ℕ)
    (blocks : Fin B → Mat T) (E : Execution n B) (A : Mat n)
    (b initial : Vec n) : ℕ → Vec n
  | 0 => initial
  | k + 1 => jacobiStep layout S blocks E A b
      (iterates layout S blocks E A b initial k) k

def error (layout : Fin n ≃ Fin B × Fin T) (S : ℕ)
    (blocks : Fin B → Mat T) (E : Execution n B) (A : Mat n)
    (b initial x : Vec n) (k : ℕ) : Vec n :=
  iterates layout S blocks E A b initial k - x

/-- Max absolute entry; the empty-vector convention is zero. -/
def vectorInfNorm (v : Vec n) : ℝ :=
  ((Finset.univ.sup (fun i : Fin n => (⟨|v i|, abs_nonneg _⟩ : NNReal)) : NNReal) : ℝ)

/-- Induced infinity norm: maximum absolute row sum, not Mathlib's default
matrix norm. The empty-matrix convention is zero. -/
def matrixInfNorm (A : Mat n) : ℝ :=
  ((Finset.univ.sup (fun i : Fin n =>
    (⟨∑ j, |A i j|, Finset.sum_nonneg (fun j _ => abs_nonneg (A i j))⟩ : NNReal)) : NNReal) : ℝ)

def matrixAbs (A : Mat n) : Mat n := fun i j => |A i j|

def gamma (m : ℕ) (u : ℝ) : ℝ := (m : ℝ) * u / (1 - (m : ℝ) * u)

def c₁ (n S : ℕ) (us : ℝ) : ℝ :=
  gamma (S + n / S - 1) us + us + us * gamma (S + n / S - 1) us

def c₂ (T : ℕ) (uc : ℝ) : ℝ := gamma T uc ^ 2 + 3 * gamma (T + 1) uc

/-- D⁻¹ is the genuine matrix inverse, not an independently supplied majorant. -/
def gain (T : ℕ) (uc : ℝ) (D R : Mat n) : Mat n :=
  c₂ T uc • (matrixAbs D⁻¹ * matrixAbs R.transpose * matrixAbs R)

def eta (T : ℕ) (uc : ℝ) (D R : Mat n) : ℝ := matrixInfNorm (gain T uc D R)
def q (D N : Mat n) : ℝ := matrixInfNorm (D⁻¹ * N)
def p (D A : Mat n) : ℝ := matrixInfNorm (matrixAbs D⁻¹ * matrixAbs A)

def alpha (n S T : ℕ) (us uc : ℝ) (A D N R : Mat n) : ℝ :=
  (eta T uc D R + us + (1 + us) * (q D N + uc * p D A)) / (1 - eta T uc D R)
    + us + (1 + us) * (1 + uc) * c₁ n S us * p D A / (1 - eta T uc D R)

def beta (n S T : ℕ) (us uc : ℝ) (A D R : Mat n) (x b : Vec n) : ℝ :=
  (us + (1 + us) * (1 + uc) * c₁ n S us * p D A / (1 - eta T uc D R))
      * vectorInfNorm x
    + (1 + us) * (1 + uc) * us / (1 - eta T uc D R)
      * matrixInfNorm D⁻¹ * vectorInfNorm b


lemma subTape_admissible {u : ℝ} {t : Tape} (h : TapeAdmissible u t)
    (pre : List ℕ) : TapeAdmissible u (subTape pre t) :=
  fun address => h (pre ++ address)

lemma rounded_error {u : ℝ} {t : Tape} (h : TapeAdmissible u t)
    (address : List ℕ) (z : ℝ) : |rounded t address z - z| ≤ u * |z| := by
  have heq : rounded t address z - z = t address * z := by unfold rounded; ring
  rw [heq, abs_mul]
  exact mul_le_mul_of_nonneg_right (h address) (abs_nonneg z)

lemma rounded_abs {u : ℝ} {t : Tape} (h : TapeAdmissible u t)
    (address : List ℕ) (z : ℝ) : |rounded t address z| ≤ (1 + u) * |z| := by
  calc
    |rounded t address z| = |z + (rounded t address z - z)| := by congr 1; ring
    _ ≤ |z| + |rounded t address z - z| := abs_add_le _ _
    _ ≤ |z| + u * |z| := add_le_add le_rfl (rounded_error h address z)
    _ = (1 + u) * |z| := by ring

lemma vectorInfNorm_nonneg (v : Vec n) : 0 ≤ vectorInfNorm v := NNReal.coe_nonneg _
lemma matrixInfNorm_nonneg (A : Mat n) : 0 ≤ matrixInfNorm A := NNReal.coe_nonneg _

lemma abs_le_vectorInfNorm (v : Vec n) (i : Fin n) : |v i| ≤ vectorInfNorm v := by
  exact_mod_cast (Finset.le_sup (f := fun i : Fin n =>
    (⟨|v i|, abs_nonneg _⟩ : NNReal)) (Finset.mem_univ i))

lemma vectorInfNorm_le {v : Vec n} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i, |v i| ≤ r) : vectorInfNorm v ≤ r := by
  change ((Finset.univ.sup (fun i : Fin n =>
    (⟨|v i|, abs_nonneg _⟩ : NNReal)) : NNReal) : ℝ) ≤ r
  exact_mod_cast (Finset.sup_le (a := (⟨r, hr⟩ : NNReal))
    (fun i _ => show (⟨|v i|, abs_nonneg _⟩ : NNReal) ≤ (⟨r, hr⟩ : NNReal) from h i))

lemma rowSum_le_matrixInfNorm (A : Mat n) (i : Fin n) :
    ∑ j, |A i j| ≤ matrixInfNorm A := by
  exact_mod_cast (Finset.le_sup (f := fun i : Fin n =>
    (⟨∑ j, |A i j|, Finset.sum_nonneg (fun j _ => abs_nonneg (A i j))⟩ : NNReal))
    (Finset.mem_univ i))

lemma vectorInfNorm_add_le (v w : Vec n) :
    vectorInfNorm (v + w) ≤ vectorInfNorm v + vectorInfNorm w := by
  apply vectorInfNorm_le (add_nonneg (vectorInfNorm_nonneg _) (vectorInfNorm_nonneg _))
  intro i
  exact (abs_add_le (v i) (w i)).trans
    (add_le_add (abs_le_vectorInfNorm v i) (abs_le_vectorInfNorm w i))

lemma vectorInfNorm_mulVec_le (A : Mat n) (v : Vec n) :
    vectorInfNorm (A.mulVec v) ≤ matrixInfNorm A * vectorInfNorm v := by
  apply vectorInfNorm_le (mul_nonneg (matrixInfNorm_nonneg _) (vectorInfNorm_nonneg _))
  intro i
  change |∑ j, A i j * v j| ≤ _
  calc
    |∑ j, A i j * v j| ≤ ∑ j, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |A i j| * vectorInfNorm v := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_le_vectorInfNorm v j) (abs_nonneg _)
    _ = (∑ j, |A i j|) * vectorInfNorm v := (Finset.sum_mul _ _ _).symm
    _ ≤ matrixInfNorm A * vectorInfNorm v :=
      mul_le_mul_of_nonneg_right (rowSum_le_matrixInfNorm A i) (vectorInfNorm_nonneg _)

lemma gamma_nonneg {m : ℕ} {u : ℝ} (hu : 0 ≤ u) (hm : (m : ℝ) * u < 1) :
    0 ≤ gamma m u :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (sub_pos.mpr hm).le

lemma gamma_mono {m k : ℕ} {u : ℝ} (hu : 0 ≤ u) (hmk : m ≤ k)
    (hk : (k : ℝ) * u < 1) : gamma m u ≤ gamma k u := by
  have hmk' : (m : ℝ) * u ≤ (k : ℝ) * u :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hmk) hu
  unfold gamma
  apply (div_le_div_iff₀ (by linarith : 0 < 1 - (m : ℝ) * u)
    (sub_pos.mpr hk)).mpr
  nlinarith

lemma c₁_nonneg {n S : ℕ} {us : ℝ} (hu : 0 ≤ us)
    (hg : ((S + n / S - 1 : ℕ) : ℝ) * us < 1) : 0 ≤ c₁ n S us := by
  unfold c₁
  positivity [gamma_nonneg hu hg]

lemma c₂_nonneg {T : ℕ} {uc : ℝ} (hu : 0 ≤ uc)
    (hg : ((T + 1 : ℕ) : ℝ) * uc < 1) : 0 ≤ c₂ T uc := by
  unfold c₂
  positivity [gamma_nonneg hu hg]

lemma cholesky_constant_le {T : ℕ} {uc : ℝ} (hu : 0 ≤ uc)
    (hg : ((T + 1 : ℕ) : ℝ) * uc < 1) :
    gamma (T + 1) uc + 2 * gamma T uc + gamma T uc ^ 2 ≤ c₂ T uc := by
  have h := gamma_mono hu (Nat.le_succ T) hg
  unfold c₂
  linarith

lemma alpha_nonneg {n S T : ℕ} {us uc : ℝ} {A D N R : Mat n}
    (hus : 0 ≤ us) (huc : 0 ≤ uc)
    (hg : ((S + n / S - 1 : ℕ) : ℝ) * us < 1)
    (heta : eta T uc D R < 1) : 0 ≤ alpha n S T us uc A D N R := by
  have hη : 0 ≤ eta T uc D R := matrixInfNorm_nonneg _
  have hq : 0 ≤ q D N := matrixInfNorm_nonneg _
  have hp : 0 ≤ p D A := matrixInfNorm_nonneg _
  have hc : 0 ≤ c₁ n S us := c₁_nonneg hus hg
  have hd : 0 < 1 - eta T uc D R := sub_pos.mpr heta
  unfold alpha
  positivity

lemma beta_nonneg {n S T : ℕ} {us uc : ℝ} {A D R : Mat n} {x b : Vec n}
    (hus : 0 ≤ us) (huc : 0 ≤ uc)
    (hg : ((S + n / S - 1 : ℕ) : ℝ) * us < 1)
    (heta : eta T uc D R < 1) : 0 ≤ beta n S T us uc A D R x b := by
  have hp : 0 ≤ p D A := matrixInfNorm_nonneg _
  have hc : 0 ≤ c₁ n S us := c₁_nonneg hus hg
  have hd : 0 < 1 - eta T uc D R := sub_pos.mpr heta
  have hx := vectorInfNorm_nonneg x
  have hb := vectorInfNorm_nonneg b
  have hD := matrixInfNorm_nonneg D⁻¹
  unfold beta
  positivity

/-- Scalar absorption needed for the computed correction, without constructing
an inverse of I-G. -/
lemma absorb_feedback {C L η : ℝ} (hη : η < 1) (h : C ≤ L + η * C) :
    C ≤ L / (1 - η) := by
  apply (le_div_iff₀ (sub_pos.mpr hη)).mpr
  nlinarith

/-- An independent scalar lemma; its recurrence premise must be established
from the actual arithmetic kernels before applying it to the selected target. -/
lemma recurrence_finite_bound {f : ℕ → ℝ} {a d : ℝ} (ha : 0 ≤ a)
    (halt : a < 1) (hstep : ∀ k, f (k + 1) ≤ a * f k + d) :
    ∀ k, f k ≤ a ^ k * f 0 + (1 - a ^ k) / (1 - a) * d := by
  have hden : 1 - a ≠ 0 := ne_of_gt (sub_pos.mpr halt)
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      f (k + 1) ≤ a * f k + d := hstep k
      _ ≤ a * (a ^ k * f 0 + (1 - a ^ k) / (1 - a) * d) + d :=
        add_le_add (mul_le_mul_of_nonneg_left ih ha) le_rfl
      _ = a ^ (k + 1) * f 0 + (1 - a ^ (k + 1)) / (1 - a) * d := by
        rw [pow_succ]
        field_simp
        ring

lemma recurrence_limsup_bound {f : ℕ → ℝ} {a d : ℝ} (hf : ∀ k, 0 ≤ f k)
    (ha : 0 ≤ a) (halt : a < 1) (hstep : ∀ k, f (k + 1) ≤ a * f k + d) :
    Filter.limsup f Filter.atTop ≤ d / (1 - a) := by
  have hpower : Filter.Tendsto (fun k : ℕ => a ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha halt
  have hlim : Filter.Tendsto
      (fun k : ℕ => a ^ k * f 0 + (1 - a ^ k) / (1 - a) * d)
      Filter.atTop (nhds (d / (1 - a))) := by
    convert (hpower.mul_const (f 0)).add
      (((tendsto_const_nhds.sub hpower).div_const (1 - a)).mul_const d) using 1 <;> simp [div_eq_mul_inv, mul_comm]
  have hbelow : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop f := by
    exact Filter.isCoboundedUnder_le_of_le Filter.atTop hf
  have hcompare := Filter.limsup_le_limsup
    (Filter.Eventually.of_forall (recurrence_finite_bound ha halt hstep))
    hbelow hlim.isBoundedUnder_le
  rw [hlim.limsup_eq] at hcompare
  exact hcompare

lemma rounding_factor_bounds {u δ : ℝ} (hu : 0 ≤ u) (hu1 : u < 1)
    (hδ : |δ| ≤ u) : 1 - u ≤ 1 + δ ∧ 1 + δ ≤ 1 / (1 - u) := by
  rcases abs_le.mp hδ with ⟨hδlo, hδhi⟩
  constructor
  · linarith
  · apply (le_div_iff₀ (sub_pos.mpr hu1)).mpr
    nlinarith [sq_nonneg u]

lemma inverse_rounding_factor_bounds {u δ : ℝ} (hu : 0 ≤ u) (hu1 : u < 1)
    (hδ : |δ| ≤ u) : 1 - u ≤ 1 / (1 + δ) ∧ 1 / (1 + δ) ≤ 1 / (1 - u) := by
  rcases abs_le.mp hδ with ⟨hδlo, hδhi⟩
  have hd : 0 < 1 + δ := by linarith
  constructor
  · apply (le_div_iff₀ hd).mpr
    have h : (1 - u) * (1 + δ) ≤ (1 - u) * (1 + u) :=
      mul_le_mul_of_nonneg_left (by linarith) (sub_pos.mpr hu1).le
    nlinarith [sq_nonneg u]
  · apply one_div_le_one_div_of_le (sub_pos.mpr hu1)
    linarith

/-- A product of direct or inverse local rounding factors. The interval
hypothesis is proved for both kinds of factor immediately above. -/
lemma product_rounding_bounds (zs : List ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hvalid : (zs.length : ℝ) * u < 1)
    (hz : ∀ z ∈ zs, 1 - u ≤ z ∧ z ≤ 1 / (1 - u)) :
    1 - (zs.length : ℝ) * u ≤ zs.prod ∧
      zs.prod ≤ 1 / (1 - (zs.length : ℝ) * u) := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    have hlen : ((z :: zs).length : ℝ) = (zs.length : ℝ) + 1 := by simp
    have htail : (zs.length : ℝ) * u < 1 := by
      rw [hlen] at hvalid
      nlinarith
    have hu1 : u < 1 := by
      rw [hlen] at hvalid
      nlinarith [mul_nonneg (Nat.cast_nonneg zs.length) hu]
    have hden : 0 < 1 - (zs.length : ℝ) * u := sub_pos.mpr htail
    have hden' : 0 < 1 - ((zs.length : ℝ) + 1) * u := by
      rw [hlen] at hvalid
      linarith
    have hz0 := hz z (by simp)
    have hzs := ih htail (fun x hx => hz x (List.mem_cons_of_mem _ hx))
    rw [List.prod_cons, hlen]
    constructor
    · have hlo := mul_le_mul hz0.1 hzs.1 hden.le
        (show 0 ≤ z by linarith [hz0.1])
      nlinarith [mul_nonneg (Nat.cast_nonneg zs.length) (sq_nonneg u)]
    · calc
        z * zs.prod ≤ (1 / (1 - u)) * (1 / (1 - (zs.length : ℝ) * u)) :=
          mul_le_mul hz0.2 hzs.2 (by linarith [hzs.1])
            (div_nonneg zero_le_one (sub_pos.mpr hu1).le)
        _ = 1 / ((1 - u) * (1 - (zs.length : ℝ) * u)) := by rw [div_mul_div_comm, one_mul]
        _ ≤ 1 / (1 - ((zs.length : ℝ) + 1) * u) := by
          apply one_div_le_one_div_of_le hden'
          nlinarith [mul_nonneg (Nat.cast_nonneg zs.length) (sq_nonneg u)]

lemma product_relative_error (zs : List ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hvalid : (zs.length : ℝ) * u < 1)
    (hz : ∀ z ∈ zs, 1 - u ≤ z ∧ z ≤ 1 / (1 - u)) :
    |zs.prod - 1| ≤ gamma zs.length u := by
  have hb := product_rounding_bounds zs hu hvalid hz
  have hd : 0 < 1 - (zs.length : ℝ) * u := sub_pos.mpr hvalid
  have hmu : 0 ≤ (zs.length : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hgamma : (zs.length : ℝ) * u ≤ gamma zs.length u := by
    unfold gamma
    apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg ((zs.length : ℝ) * u)]
  have hid : 1 / (1 - (zs.length : ℝ) * u) - 1 = gamma zs.length u := by
    unfold gamma
    field_simp
    ring
  exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩


lemma abs_list_sum (ids : List ℕ) (v : ℕ → ℝ) :
    |(ids.map v).sum| ≤ (ids.map (fun i => |v i|)).sum := by
  induction ids with
  | nil => simp
  | cons i ids ih =>
    simpa only [List.map_cons, List.sum_cons] using
      (abs_add_le (v i) (ids.map v).sum).trans (add_le_add le_rfl ih)

lemma abs_list_sum_nonneg (ids : List ℕ) (v : ℕ → ℝ) :
    0 ≤ (ids.map (fun i => |v i|)).sum :=
  List.sum_nonneg (by intro x hx; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)

/-- Forward error for the actual sequential accumulation loop. -/
lemma roundedFold_error {u : ℝ} {t : Tape} (hu : 0 ≤ u) (ht : TapeAdmissible u t)
    (ids : List ℕ) (v : ℕ → ℝ) (initial : ℝ) :
    |ids.foldl (fun s k => rounded t [k] (s + v k)) initial -
        (initial + (ids.map v).sum)| ≤
      ((1 + u) ^ ids.length - 1) *
        (|initial| + (ids.map (fun i => |v i|)).sum) := by
  induction ids using List.reverseRecOn with
  | nil => simp
  | append_singleton ids k ih =>
    let F := ids.foldl (fun s k => rounded t [k] (s + v k)) initial
    let V := (ids.map v).sum
    let W := (ids.map (fun i => |v i|)).sum
    have hW : 0 ≤ W := abs_list_sum_nonneg ids v
    have hV : |V| ≤ W := abs_list_sum ids v
    have hF : |F| ≤ |initial| + W + |F - (initial + V)| := by
      calc
        |F| = |initial + V + (F - (initial + V))| := by congr 1; ring
        _ ≤ |initial + V| + |F - (initial + V)| := abs_add_le _ _
        _ ≤ |initial| + W + |F - (initial + V)| :=
          add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl hV)) le_rfl
    have hr : |rounded t [k] (F + v k) - (F + v k)| ≤ u * (|F| + |v k|) :=
      (rounded_error ht [k] (F + v k)).trans
        (mul_le_mul_of_nonneg_left (abs_add_le _ _) hu)
    have hsplit :
        |rounded t [k] (F + v k) - (initial + (V + v k))| ≤
          |rounded t [k] (F + v k) - (F + v k)| + |F - (initial + V)| := by
      convert abs_add_le (rounded t [k] (F + v k) - (F + v k))
        (F - (initial + V)) using 1 <;> congr 1 <;> ring
    have hp : 1 ≤ (1 + u) ^ ids.length := one_le_pow₀ (by linarith)
    have hc : u ≤ (1 + u) ^ (ids.length + 1) - 1 := by
      rw [pow_succ]
      nlinarith
    have hi : |F - (initial + V)| ≤ ((1 + u) ^ ids.length - 1) * (|initial| + W) := ih
    have hfinal : |rounded t [k] (F + v k) - (initial + (V + v k))| ≤
        ((1 + u) ^ (ids.length + 1) - 1) * (|initial| + (W + |v k|)) := by
      rw [pow_succ] at hc ⊢
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) (abs_nonneg (v k)),
        mul_nonneg (sub_nonneg.mpr hc) (abs_nonneg (v k))]
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero, List.length_append,
      List.length_singleton] using hfinal

lemma roundedSum_error_pow {u : ℝ} {t : Tape} (hu : 0 ≤ u) (ht : TapeAdmissible u t)
    (ids : List ℕ) (v : ℕ → ℝ) :
    |roundedSum t ids v - (ids.map v).sum| ≤
      ((1 + u) ^ (ids.length - 1) - 1) * (ids.map (fun i => |v i|)).sum := by
  cases ids with
  | nil => simp [roundedSum]
  | cons j js =>
    simpa [roundedSum] using roundedFold_error hu ht js v (v j)

lemma pow_sub_one_le_gamma {u : ℝ} (hu : 0 ≤ u) {m : ℕ}
    (hm : (m : ℝ) * u < 1) : (1 + u) ^ m - 1 ≤ gamma m u := by
  by_cases hm0 : m = 0
  · subst m; simp [gamma]
  have hu1 : u < 1 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
    nlinarith
  have h := product_relative_error (List.replicate m (1 + u)) hu (by simpa using hm)
    (by intro z hz; have heq := List.eq_of_mem_replicate hz
        subst z; exact rounding_factor_bounds hu hu1 (by simpa [abs_of_nonneg hu]))
  simp only [List.prod_replicate, List.length_replicate] at h
  exact (le_abs_self ((1 + u) ^ m - 1)).trans h

lemma roundedSum_error {u : ℝ} {t : Tape} (hu : 0 ≤ u) (ht : TapeAdmissible u t)
    (ids : List ℕ) (v : ℕ → ℝ) (hvalid : ((ids.length - 1 : ℕ) : ℝ) * u < 1) :
    |roundedSum t ids v - (ids.map v).sum| ≤
      gamma (ids.length - 1) u * (ids.map (fun i => |v i|)).sum :=
  (roundedSum_error_pow hu ht ids v).trans
    (mul_le_mul_of_nonneg_right (pow_sub_one_le_gamma hu hvalid) (abs_list_sum_nonneg ids v))


lemma list_sum_map_sub (ids : List ℕ) (v w : ℕ → ℝ) :
    (ids.map (fun i => v i - w i)).sum = (ids.map v).sum - (ids.map w).sum := by
  induction ids with
  | nil => simp
  | cons i ids ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Dot-product error, proved from the local rounded multiplication and the
sequential accumulation loop, with exactly one gamma index per input entry. -/
lemma roundedDot_error {u : ℝ} {t : Tape} (hu : 0 ≤ u) (ht : TapeAdmissible u t)
    (ids : List ℕ) (a b : ℕ → ℝ) (hvalid : (ids.length : ℝ) * u < 1) :
    |roundedDot t ids a b - (ids.map (fun i => a i * b i)).sum| ≤
      gamma ids.length u * (ids.map (fun i => |a i * b i|)).sum := by
  by_cases hnil : ids = []
  · subst ids; simp [roundedDot, roundedSum]
  let v : ℕ → ℝ := fun i => a i * b i
  let w : ℕ → ℝ := fun i => rounded t [0, i] (v i)
  let W := (ids.map (fun i => |v i|)).sum
  have hW : 0 ≤ W := abs_list_sum_nonneg ids v
  have hpoint : ∀ i, |w i - v i| ≤ u * |v i| := fun i => rounded_error ht [0, i] (v i)
  have hw : (ids.map (fun i => |w i|)).sum ≤ (1 + u) * W := by
    calc
      _ ≤ (ids.map (fun i => (1 + u) * |v i|)).sum :=
        List.sum_le_sum (fun i _ => rounded_abs ht [0, i] (v i))
      _ = _ := List.sum_map_mul_left _ _ _
  have hdiff : |(ids.map w).sum - (ids.map v).sum| ≤ u * W := by
    rw [← list_sum_map_sub]
    calc
      _ ≤ (ids.map (fun i => |w i - v i|)).sum := abs_list_sum ids _
      _ ≤ (ids.map (fun i => u * |v i|)).sum := List.sum_le_sum (fun i _ => hpoint i)
      _ = _ := List.sum_map_mul_left _ _ _
  have hsum := roundedSum_error_pow hu (subTape_admissible ht [1]) ids w
  have hpow : 0 ≤ (1 + u) ^ (ids.length - 1) - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (by linarith))
  have hlen : ids.length - 1 + 1 = ids.length := by
    have hp : 0 < ids.length := List.length_pos_iff.mpr hnil
    omega
  have hidentity : ((1 + u) ^ (ids.length - 1) - 1) * ((1 + u) * W) + u * W =
      ((1 + u) ^ ids.length - 1) * W := by
    conv_rhs => rw [← hlen, pow_succ]
    ring
  change |roundedSum (subTape [1] t) ids w - (ids.map v).sum| ≤ gamma ids.length u * W
  calc
    _ ≤ |roundedSum (subTape [1] t) ids w - (ids.map w).sum| +
        |(ids.map w).sum - (ids.map v).sum| := by
      convert abs_add_le (roundedSum (subTape [1] t) ids w - (ids.map w).sum)
        ((ids.map w).sum - (ids.map v).sum) using 1 <;> congr 1 <;> ring
    _ ≤ ((1 + u) ^ (ids.length - 1) - 1) * ((1 + u) * W) + u * W :=
      add_le_add (hsum.trans (mul_le_mul_of_nonneg_left hw hpow)) hdiff
    _ = ((1 + u) ^ ids.length - 1) * W := hidentity
    _ ≤ gamma ids.length u * W := mul_le_mul_of_nonneg_right (pow_sub_one_le_gamma hu hvalid) hW


lemma roundedDot_error_pow {u : ℝ} {t : Tape} (hu : 0 ≤ u) (ht : TapeAdmissible u t)
    (ids : List ℕ) (a b : ℕ → ℝ) :
    |roundedDot t ids a b - (ids.map (fun i => a i * b i)).sum| ≤
      ((1 + u) ^ ids.length - 1) * (ids.map (fun i => |a i * b i|)).sum := by
  by_cases hnil : ids = []
  · subst ids; simp [roundedDot, roundedSum]
  let v : ℕ → ℝ := fun i => a i * b i
  let w : ℕ → ℝ := fun i => rounded t [0, i] (v i)
  let W := (ids.map (fun i => |v i|)).sum
  have hW : 0 ≤ W := abs_list_sum_nonneg ids v
  have hpoint : ∀ i, |w i - v i| ≤ u * |v i| := fun i => rounded_error ht [0, i] (v i)
  have hw : (ids.map (fun i => |w i|)).sum ≤ (1 + u) * W := by
    calc
      _ ≤ (ids.map (fun i => (1 + u) * |v i|)).sum :=
        List.sum_le_sum (fun i _ => rounded_abs ht [0, i] (v i))
      _ = _ := List.sum_map_mul_left _ _ _
  have hdiff : |(ids.map w).sum - (ids.map v).sum| ≤ u * W := by
    rw [← list_sum_map_sub]
    calc
      _ ≤ (ids.map (fun i => |w i - v i|)).sum := abs_list_sum ids _
      _ ≤ (ids.map (fun i => u * |v i|)).sum := List.sum_le_sum (fun i _ => hpoint i)
      _ = _ := List.sum_map_mul_left _ _ _
  have hsum := roundedSum_error_pow hu (subTape_admissible ht [1]) ids w
  have hpow : 0 ≤ (1 + u) ^ (ids.length - 1) - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (by linarith))
  have hlen : ids.length - 1 + 1 = ids.length := by
    have hp : 0 < ids.length := List.length_pos_iff.mpr hnil
    omega
  have hidentity : ((1 + u) ^ (ids.length - 1) - 1) * ((1 + u) * W) + u * W =
      ((1 + u) ^ ids.length - 1) * W := by
    conv_rhs => rw [← hlen, pow_succ]
    ring
  change |roundedSum (subTape [1] t) ids w - (ids.map v).sum| ≤ ((1 + u) ^ ids.length - 1) * W
  calc
    _ ≤ |roundedSum (subTape [1] t) ids w - (ids.map w).sum| +
        |(ids.map w).sum - (ids.map v).sum| := by
      convert abs_add_le (roundedSum (subTape [1] t) ids w - (ids.map w).sum)
        ((ids.map w).sum - (ids.map v).sum) using 1 <;> congr 1 <;> ring
    _ ≤ ((1 + u) ^ (ids.length - 1) - 1) * ((1 + u) * W) + u * W :=
      add_le_add (hsum.trans (mul_le_mul_of_nonneg_left hw hpow)) hdiff
    _ = ((1 + u) ^ ids.length - 1) * W := hidentity

/-- The error of the actual two-level reduction before reindexing its tiles. -/
lemma tiledDot_error_tiles {u : ℝ} {t : Tape} (hu : 0 ≤ u)
    (ht : TapeAdmissible u t) (S : ℕ) (a b : Vec n) :
    |tiledDot S t a b -
      ((List.range (n / S)).map (fun tile =>
        ((List.range S).map (fun j =>
          entry a (tile * S + j) * entry b (tile * S + j))).sum)).sum| ≤
    ((1 + u) ^ (S + (n / S - 1)) - 1) *
      ((List.range (n / S)).map (fun tile =>
        ((List.range S).map (fun j =>
          |entry a (tile * S + j) * entry b (tile * S + j)|)).sum)).sum := by
  let ids := List.range (n / S)
  let v : ℕ → ℝ := fun tile => ((List.range S).map (fun j =>
    entry a (tile * S + j) * entry b (tile * S + j))).sum
  let w : ℕ → ℝ := fun tile => roundedDot (subTape [0, tile] t) (List.range S)
    (fun j => entry a (tile * S + j)) (fun j => entry b (tile * S + j))
  let M : ℕ → ℝ := fun tile => ((List.range S).map (fun j =>
    |entry a (tile * S + j) * entry b (tile * S + j)|)).sum
  let W := (ids.map M).sum
  have hM : ∀ i, 0 ≤ M i := fun i => abs_list_sum_nonneg _ _
  have hW : 0 ≤ W := List.sum_nonneg (by
    intro z hz
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
    exact hM i)
  have hpow : 0 ≤ (1 + u) ^ S - 1 := sub_nonneg.mpr (one_le_pow₀ (by linarith))
  have hv : ∀ i, |v i| ≤ M i := fun i => abs_list_sum _ _
  have hpoint : ∀ i, |w i - v i| ≤ ((1 + u) ^ S - 1) * M i := by
    intro i
    simpa only [List.length_range] using
      roundedDot_error_pow hu (subTape_admissible ht [0, i]) (List.range S)
        (fun j => entry a (i * S + j)) (fun j => entry b (i * S + j))
  have hw : ∀ i, |w i| ≤ (1 + u) ^ S * M i := by
    intro i
    calc
      |w i| = |v i + (w i - v i)| := by congr 1; ring
      _ ≤ |v i| + |w i - v i| := abs_add_le _ _
      _ ≤ M i + ((1 + u) ^ S - 1) * M i := add_le_add (hv i) (hpoint i)
      _ = (1 + u) ^ S * M i := by ring
  have hws : (ids.map (fun i => |w i|)).sum ≤ (1 + u) ^ S * W := by
    calc
      _ ≤ (ids.map (fun i => (1 + u) ^ S * M i)).sum :=
        List.sum_le_sum (fun i _ => hw i)
      _ = _ := List.sum_map_mul_left _ _ _
  have hdiff : |(ids.map w).sum - (ids.map v).sum| ≤
      ((1 + u) ^ S - 1) * W := by
    rw [← list_sum_map_sub]
    calc
      _ ≤ (ids.map (fun i => |w i - v i|)).sum := abs_list_sum _ _
      _ ≤ (ids.map (fun i => ((1 + u) ^ S - 1) * M i)).sum :=
        List.sum_le_sum (fun i _ => hpoint i)
      _ = _ := List.sum_map_mul_left _ _ _
  have hr := roundedSum_error_pow hu (subTape_admissible ht [1]) ids w
  have houter : 0 ≤ (1 + u) ^ (ids.length - 1) - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (by linarith))
  change |roundedSum (subTape [1] t) ids w - (ids.map v).sum| ≤
    ((1 + u) ^ (S + (n / S - 1)) - 1) * W
  calc
    _ ≤ |roundedSum (subTape [1] t) ids w - (ids.map w).sum| +
        |(ids.map w).sum - (ids.map v).sum| := by
      convert abs_add_le (roundedSum (subTape [1] t) ids w - (ids.map w).sum)
        ((ids.map w).sum - (ids.map v).sum) using 1 <;> congr 1 <;> ring
    _ ≤ ((1 + u) ^ (ids.length - 1) - 1) * ((1 + u) ^ S * W) +
        ((1 + u) ^ S - 1) * W :=
      add_le_add (hr.trans (mul_le_mul_of_nonneg_left hws houter)) hdiff
    _ = _ := by simp only [ids, List.length_range, pow_add]; ring

lemma list_range_sum_tiles (K S : ℕ) (f : ℕ → ℝ) :
    ((List.range K).map (fun tile =>
      ((List.range S).map (fun j => f (tile * S + j))).sum)).sum =
      ((List.range (K * S)).map f).sum := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, ih, Nat.succ_mul, List.range_add, List.map_append,
      List.sum_append, List.map_map]
    congr 1

lemma list_range_sum (K : ℕ) (f : ℕ → ℝ) :
    ((List.range K).map f).sum = ∑ i ∈ Finset.range K, f i := by
  induction K with
  | zero => simp
  | succ K ih => simp [List.range_succ, Finset.sum_range_succ, ih]


lemma tiledDot_error {u : ℝ} {t : Tape} (hu : 0 ≤ u)
    (ht : TapeAdmissible u t) (hS : 0 < S) (hdiv : S ∣ n)
    (hvalid : ((S + n / S - 1 : ℕ) : ℝ) * u < 1) (a b : Vec n) :
    |tiledDot S t a b - ∑ j, a j * b j| ≤
      gamma (S + n / S - 1) u * ∑ j, |a j * b j| := by
  by_cases hn : n = 0
  · subst n
    simp [tiledDot, roundedSum]
  have hK : 0 < n / S := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv) hS
  have hindex : S + (n / S - 1) = S + n / S - 1 := by omega
  have hprod : n / S * S = n := Nat.div_mul_cancel hdiv
  have hflatten : ∀ f : ℕ → ℝ,
      ((List.range (n / S)).map (fun tile =>
        ((List.range S).map (fun j => f (tile * S + j))).sum)).sum =
        ((List.range n).map f).sum := by
    intro f
    rw [list_range_sum_tiles, hprod]
  have hexact : ((List.range n).map (fun j => entry a j * entry b j)).sum =
      ∑ j, a j * b j := by
    rw [list_range_sum, ← Fin.sum_univ_eq_sum_range]
    simp [entry]
  have hmajor : ((List.range n).map (fun j => |entry a j * entry b j|)).sum =
      ∑ j, |a j * b j| := by
    rw [list_range_sum, ← Fin.sum_univ_eq_sum_range]
    simp [entry]
  have h := tiledDot_error_tiles hu ht S a b
  rw [hflatten (fun j => entry a j * entry b j),
    hflatten (fun j => |entry a j * entry b j|), hexact, hmajor, hindex] at h
  exact h.trans (mul_le_mul_of_nonneg_right (pow_sub_one_le_gamma hu hvalid)
    (Finset.sum_nonneg (fun j _ => abs_nonneg _)))


lemma blockDiagonal_isUnit (layout : Fin n ≃ Fin B × Fin T)
    (blocks : Fin B → Mat T) (hSPD : ∀ l, (blocks l).PosDef) :
    IsUnit (blockDiagonal layout blocks) := by
  have hb : IsUnit blocks := Pi.isUnit_iff.mpr (fun l => (hSPD l).isUnit)
  have hd := hb.map (Matrix.blockDiagonalRingHom (Fin T) (Fin B) ℝ)
  have hr := hd.map (Matrix.reindexAlgEquiv ℝ ℝ
    (layout.trans (Equiv.prodComm (Fin B) (Fin T))).symm).toRingHom
  exact hr

lemma blockDiagonal_inv_mul (layout : Fin n ≃ Fin B × Fin T)
    (blocks : Fin B → Mat T) (hSPD : ∀ l, (blocks l).PosDef) :
    (blockDiagonal layout blocks)⁻¹ * blockDiagonal layout blocks = 1 := by
  apply Matrix.nonsing_inv_mul
  exact (Matrix.isUnit_iff_isUnit_det _).mp (blockDiagonal_isUnit layout blocks hSPD)

lemma blockDiagonal_mul_inv (layout : Fin n ≃ Fin B × Fin T)
    (blocks : Fin B → Mat T) (hSPD : ∀ l, (blocks l).PosDef) :
    blockDiagonal layout blocks * (blockDiagonal layout blocks)⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  exact (Matrix.isUnit_iff_isUnit_det _).mp (blockDiagonal_isUnit layout blocks hSPD)


/-- Componentwise residual subtraction: the local tape error is allowed to
differ in every row. -/
lemma rounded_residual_perturbation {u g : ℝ} {t : Tape}
    (hu : 0 ≤ u) (hg : 0 ≤ g) (ht : TapeAdmissible u t)
    (b y z M : ℝ) (hM : 0 ≤ M) (hy : |y| ≤ M) (hz : |z - y| ≤ g * M) :
    |t [] * b| ≤ u * |b| ∧
    |rounded t [] (b - z) - (b - y) - t [] * b| ≤ (g + u + u * g) * M := by
  have hδ := ht []
  have hfac : |1 + t []| ≤ 1 + u := by
    simpa only [abs_one] using (abs_add_le (1 : ℝ) (t [])).trans (add_le_add le_rfl hδ)
  constructor
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hδ (abs_nonneg b)
  · have heq : rounded t [] (b - z) - (b - y) - t [] * b =
        -((z - y) * (1 + t []) + t [] * y) := by unfold rounded; ring
    rw [heq, abs_neg]
    calc
      |(z - y) * (1 + t []) + t [] * y| ≤
          |z - y| * |1 + t []| + |t []| * |y| := by
        simpa only [abs_mul] using abs_add_le ((z - y) * (1 + t [])) (t [] * y)
      _ ≤ (g * M) * (1 + u) + u * M :=
        add_le_add (mul_le_mul hz hfac (abs_nonneg _) (mul_nonneg hg hM))
          (mul_le_mul hδ hy (abs_nonneg _) hu)
      _ = (g + u + u * g) * M := by ring

lemma computedResidual_perturbations {n B S : ℕ} {us : ℝ} (hus : 0 ≤ us)
    (hg : ((S + n / S - 1 : ℕ) : ℝ) * us < 1)
    (E : Execution n B) (A : Mat n) (b v : Vec n) (k : ℕ)
    (hr : ∀ i, TapeAdmissible us (E.residual k i))
    (M : Vec n) (hM : ∀ i, 0 ≤ M i)
    (hAv : ∀ i, |A.mulVec v i| ≤ M i)
    (hmv : ∀ i, |tiledMatvec S (E.matvec k) A v i - A.mulVec v i| ≤
      gamma (S + n / S - 1) us * M i) :
    ∃ db dz : Vec n,
      computedResidual S E A b v k = (b - A.mulVec v) + db + dz ∧
      (∀ i, |db i| ≤ us * |b i|) ∧ (∀ i, |dz i| ≤ c₁ n S us * M i) := by
  let db : Vec n := fun i => E.residual k i [] * b i
  let dz : Vec n := fun i => computedResidual S E A b v k i -
    (b i - A.mulVec v i) - db i
  refine ⟨db, dz, ?_, ?_, ?_⟩
  · ext i
    change computedResidual S E A b v k i =
      (b i - A.mulVec v i) + db i +
        (computedResidual S E A b v k i - (b i - A.mulVec v i) - db i)
    ring
  · intro i
    exact (rounded_residual_perturbation hus (gamma_nonneg hus hg) (hr i)
      (b i) (A.mulVec v i) (tiledMatvec S (E.matvec k) A v i) (M i)
      (hM i) (hAv i) (hmv i)).1
  · intro i
    exact (rounded_residual_perturbation hus (gamma_nonneg hus hg) (hr i)
      (b i) (A.mulVec v i) (tiledMatvec S (E.matvec k) A v i) (M i)
      (hM i) (hAv i) (hmv i)).2

/-- Componentwise bound from the concrete full-tile matrix-vector kernel. -/
lemma tiledMatvec_error {us : ℝ} (hus : 0 ≤ us)
    (hS : 0 < S) (hdiv : S ∣ n)
    (hgammaS : ((S + n / S - 1 : ℕ) : ℝ) * us < 1)
    (t : Fin n → Tape) (ht : ∀ i, TapeAdmissible us (t i))
    (A : Mat n) (v : Vec n) (i : Fin n) :
    |tiledMatvec S t A v i - A.mulVec v i| ≤
      gamma (S + n / S - 1) us *
        (matrixAbs A).mulVec (fun j => |v j|) i := by
  simpa only [tiledMatvec, Matrix.mulVec, dotProduct, matrixAbs, abs_mul] using
    tiledDot_error hus (ht i) hS hdiv hgammaS (A i) v

/-- Residual perturbations derived from the executed kernel and the exact
solution, rather than from a separate matvec-error hypothesis. -/
lemma computedResidual_backward_error {n B S : ℕ} {us : ℝ}
    (hus : 0 ≤ us) (hS : 0 < S) (hdiv : S ∣ n)
    (hgammaS : ((S + n / S - 1 : ℕ) : ℝ) * us < 1)
    (E : Execution n B) (A : Mat n) (b x v : Vec n) (k : ℕ)
    (hsolution : A.mulVec x = b)
    (hm : ∀ i, TapeAdmissible us (E.matvec k i))
    (hr : ∀ i, TapeAdmissible us (E.residual k i)) :
    ∃ db dz : Vec n,
      computedResidual S E A b v k = -A.mulVec (v - x) + db + dz ∧
      (∀ i, |db i| ≤ us * |b i|) ∧
      (∀ i, |dz i| ≤ c₁ n S us * (matrixAbs A).mulVec (fun j => |v j|) i) := by
  let M : Vec n := (matrixAbs A).mulVec (fun j => |v j|)
  have hM : ∀ i, 0 ≤ M i := by
    intro i
    change 0 ≤ ∑ j, |A i j| * |v j|
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hAv : ∀ i, |A.mulVec v i| ≤ M i := by
    intro i
    change |∑ j, A i j * v j| ≤ ∑ j, |A i j| * |v j|
    simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => A i j * v j) Finset.univ
  obtain ⟨db, dz, heq, hdb, hdz⟩ := computedResidual_perturbations hus hgammaS
    E A b v k hr M hM hAv (fun i => tiledMatvec_error hus hS hdiv hgammaS
      (E.matvec k) hm A v i)
  refine ⟨db, dz, ?_, hdb, hdz⟩
  rw [heq, Matrix.mulVec_sub, hsolution]
  congr 2
  abel


lemma convertedResidual_error {us uc : ℝ} {E : Execution n B}
    (hE : E.Admissible us uc) (r : Vec n) (k : ℕ) (i : Fin n) :
    |convertedResidual E r k i - r i| ≤ uc * |r i| :=
  rounded_error (hE.2.2.2.1 k i) [] (r i)

lemma jacobiStep_rounding_error {us uc : ℝ} {E : Execution n B}
    (hE : E.Admissible us uc) (layout : Fin n ≃ Fin B × Fin T) (S : ℕ)
    (blocks : Fin B → Mat T) (A : Mat n) (b v : Vec n) (k : ℕ) (i : Fin n) :
    let c := computedCorrection layout blocks E (computedResidual S E A b v k) k
    |jacobiStep layout S blocks E A b v k i - (v i + c i)| ≤ us * |v i + c i| :=
  rounded_error (hE.2.2.2.2.2.2 k i) [] _


/-- Full selected result. No algorithmic backward-error bound or error recurrence
is assumed: all iterates and factors are the outputs of the kernels above.
Nonnegative unit roundoffs and strictly positive gamma denominators make the
source's precision and 'all relevant gamma constants are defined' assumptions explicit.
The existence of computed Cholesky factors means successful factorization, as
in the source's Cholesky helper. -/
theorem mixed_precision_update_form_block_jacobi_in_floating_point_arithmetic
    {n B T S : ℕ}
    (layout : Fin n ≃ Fin B × Fin T)
    (hT : 0 < T) (hS : 0 < S) (hdiv : S ∣ n)
    (blocks : Fin B → Mat T) (hSPD : ∀ l, (blocks l).PosDef)
    (A N : Mat n) (hdecomp : A = blockDiagonal layout blocks + N)
    (b x initial : Vec n) (hsolution : A.mulVec x = b)
    (us uc : ℝ) (hus : 0 ≤ us) (hprecision : us < uc)
    (hgammaS : ((S + n / S - 1 : ℕ) : ℝ) * us < 1)
    (hgammaC : ((T + 1 : ℕ) : ℝ) * uc < 1)
    (E : Execution n B) (hround : E.Admissible us uc)
    (hsuccess : ∀ l, (cholesky (E.factor l) (blocks l)).isSome = true)
    (hfeedback : eta T uc (blockDiagonal layout blocks)
      (computedFactors layout blocks E) < 1) :
    let D := blockDiagonal layout blocks
    let R := computedFactors layout blocks E
    let a := alpha n S T us uc A D N R
    let d := beta n S T us uc A D R x b
    let e := error layout S blocks E A b initial x
    (∀ k : ℕ, vectorInfNorm (e (k + 1)) ≤ a * vectorInfNorm (e k) + d) ∧
    (a < 1 →
      (∀ k : ℕ, vectorInfNorm (e k) ≤ a ^ k * vectorInfNorm (e 0)
        + (1 - a ^ k) / (1 - a) * d) ∧
      Filter.limsup (fun k : ℕ => vectorInfNorm (e k)) Filter.atTop ≤ d / (1 - a)) := by
  dsimp only
  have ha : 0 ≤ alpha n S T us uc A (blockDiagonal layout blocks) N
      (computedFactors layout blocks E) :=
    alpha_nonneg hus (le_trans hus hprecision.le) hgammaS hfeedback
  have hstep : ∀ k : ℕ,
      vectorInfNorm (error layout S blocks E A b initial x (k + 1)) ≤
        alpha n S T us uc A (blockDiagonal layout blocks) N
          (computedFactors layout blocks E) *
          vectorInfNorm (error layout S blocks E A b initial x k) +
        beta n S T us uc A (blockDiagonal layout blocks)
          (computedFactors layout blocks E) x b := by
    sorry
  exact ⟨hstep, fun hlt =>
    ⟨recurrence_finite_bound ha hlt hstep,
      recurrence_limsup_bound (fun _ => vectorInfNorm_nonneg _) ha hlt hstep⟩⟩

end MixedPrecisionBlockJacobi
