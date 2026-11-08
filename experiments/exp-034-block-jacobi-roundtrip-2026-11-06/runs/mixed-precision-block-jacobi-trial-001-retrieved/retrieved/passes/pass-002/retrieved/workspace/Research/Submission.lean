import Mathlib

/-!
Formal statement of the selected mixed-precision update-form block Jacobi theorem.
All floating-point computations below are real-valued executions of elementary rounded
operations. The model laws express the no-overflow/no-underflow regime. No backward
error estimate or recurrence estimate is an input assumption.
-/
noncomputable section
open scoped BigOperators

namespace MixedPrecisionBlockJacobi

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Maximum absolute entry, also defined for the empty vector. -/
def vectorInf {n : ℕ} (v : Vec n) : ℝ :=
  (Finset.univ.sup (fun i => Real.toNNReal |v i|) : NNReal)

/-- Induced infinity norm: maximum absolute row sum, not the matrix entry norm. -/
def matrixInf {n : ℕ} (A : Mat n) : ℝ :=
  (Finset.univ.sup (fun i => Real.toNNReal (∑ j, |A i j|)) : NNReal)

def matrixAbs {n : ℕ} (A : Mat n) : Mat n := fun i j => |A i j|

def gamma (m : ℕ) (u : ℝ) : ℝ := (m : ℝ) * u / (1 - (m : ℝ) * u)

def c₁ (n S : ℕ) (us : ℝ) : ℝ :=
  gamma (S + n / S - 1) us + us + us * gamma (S + n / S - 1) us

def c₂ (T : ℕ) (uc : ℝ) : ℝ := (gamma T uc) ^ 2 + 3 * gamma (T + 1) uc

/-- One elementary operation in the common relative-error model. -/
def RelativeError (u exact computed : ℝ) : Prop :=
  ∃ δ : ℝ, |δ| ≤ u ∧ computed = exact * (1 + δ)

/-- Real-valued rounded arithmetic. Square root is explicitly rounded as well.
The division law is required only on nonzero denominators and square root only
on nonnegative radicands; successful Cholesky execution is specified separately. -/
structure Arithmetic (u : ℝ) where
  add : ℝ → ℝ → ℝ
  sub : ℝ → ℝ → ℝ
  mul : ℝ → ℝ → ℝ
  div : ℝ → ℝ → ℝ
  sqrt : ℝ → ℝ
  add_model : ∀ a b, RelativeError u (a + b) (add a b)
  sub_model : ∀ a b, RelativeError u (a - b) (sub a b)
  mul_model : ∀ a b, RelativeError u (a * b) (mul a b)
  div_model : ∀ a b, b ≠ 0 → RelativeError u (a / b) (div a b)
  sqrt_model : ∀ a, 0 ≤ a → RelativeError u (Real.sqrt a) (sqrt a)

/-- Conversion of a residual component to correction precision. Identity conversion
is allowed (take the rounding error to be zero). -/
structure Conversion (uc : ℝ) where
  apply : ℝ → ℝ
  model : ∀ a, RelativeError uc a (apply a)

/-- Sequential sum initialized with the first entry, without a rounded addition to zero. -/
def roundedSum {u : ℝ} (r : Arithmetic u) : List ℝ → ℝ
  | [] => 0
  | a :: as => as.foldl r.add a

def roundedDot {u : ℝ} {I : Type*} (r : Arithmetic u)
    (indices : List I) (a b : I → ℝ) : ℝ :=
  roundedSum r (indices.map (fun i => r.mul (a i) (b i)))

/-- Subtract an inner product; omit the subtraction altogether for an empty dot
product. This gives a single rounded division in the first triangular-solve row. -/
def subtractDot {u : ℝ} {I : Type*} (r : Arithmetic u)
    (indices : List I) (c : ℝ) (a b : I → ℝ) : ℝ :=
  match indices with
  | [] => c
  | _ :: _ => r.sub c (roundedDot r indices a b)

/-- Size-S tiles in the original ambient coordinates. S divides n in the theorem. -/
def tile (n S t : ℕ) : List (Fin n) :=
  ((List.finRange n).drop (t * S)).take S

/-- Products and sums inside a tile, followed by sequential reduction of tile sums. -/
def tiledMatVec {n : ℕ} {us : ℝ} (r : Arithmetic us) (S : ℕ)
    (A : Mat n) (v : Vec n) : Vec n := fun i =>
  roundedSum r ((List.range (n / S)).map (fun t =>
    roundedDot r (tile n S t) (A i) v))

/-- The original n coordinates are preserved by this explicit block indexing. -/
def blockDiagonal {n B T : ℕ} (ι : Fin n ≃ Fin B × Fin T)
    (d : Fin B → Mat T) : Mat n := fun i j =>
  if (ι i).1 = (ι j).1 then d (ι i).1 (ι i).2 (ι j).2 else 0

/-- One upper-triangular Cholesky row. Earlier rows are retained. -/
def choleskyRow {T : ℕ} {uc : ℝ} (r : Arithmetic uc)
    (d R : Mat T) (k : Fin T) : Mat T :=
  let prior := (List.finRange T).filter (fun i => i.val < k.val)
  let rad := subtractDot r prior (d k k) (fun i => R i k) (fun i => R i k)
  let diag := r.sqrt rad
  fun i j => if i = k then
    if j = k then diag
    else if k.val < j.val then
      r.div (subtractDot r prior (d k j) (fun l => R l k) (fun l => R l j)) diag
    else 0
  else R i j

/-- Partial factor before row k; this exposes the actual radicands for success. -/
def choleskyPrefix {T : ℕ} {uc : ℝ} (r : Arithmetic uc)
    (d : Mat T) (k : ℕ) : Mat T :=
  ((List.finRange T).take k).foldl (choleskyRow r d) 0

def cholesky {T : ℕ} {uc : ℝ} (r : Arithmetic uc) (d : Mat T) : Mat T :=
  choleskyPrefix r d T

/-- A successful execution, not a claim that SPD guarantees numerical success. -/
def CholeskySuccessful {T : ℕ} {uc : ℝ} (r : Arithmetic uc) (d : Mat T) : Prop :=
  ∀ k : Fin T,
    let R := choleskyPrefix r d k.val
    let prior := (List.finRange T).filter (fun i => i.val < k.val)
    let rad := subtractDot r prior (d k k) (fun i => R i k) (fun i => R i k)
    0 < rad ∧ 0 < r.sqrt rad

/-- Sequential forward substitution, using the computed upper factor transposed. -/
def forwardSolve {T : ℕ} {uc : ℝ} (r : Arithmetic uc)
    (R : Mat T) (b : Vec T) : Vec T :=
  (List.finRange T).foldl (fun y k =>
    let prior := (List.finRange T).filter (fun i => i.val < k.val)
    let yk := r.div (subtractDot r prior (b k) (fun i => R i k) y) (R k k)
    Function.update y k yk) 0

/-- Sequential backward substitution in reverse coordinate order. -/
def backwardSolve {T : ℕ} {uc : ℝ} (r : Arithmetic uc)
    (R : Mat T) (b : Vec T) : Vec T :=
  (List.finRange T).reverse.foldl (fun y k =>
    let later := ((List.finRange T).filter (fun i => k.val < i.val)).reverse
    let yk := r.div (subtractDot r later (b k) (R k) y) (R k k)
    Function.update y k yk) 0

def choleskySolve {T : ℕ} {uc : ℝ} (r : Arithmetic uc)
    (R : Mat T) (b : Vec T) : Vec T :=
  backwardSolve r R (forwardSolve r R b)

/-- Assemble the fixed factors once; all correction steps reuse them. -/
def computedFactor {n B T : ℕ} {uc : ℝ} (r : Arithmetic uc)
    (ι : Fin n ≃ Fin B × Fin T) (d : Fin B → Mat T) : Mat n :=
  blockDiagonal ι (fun l => cholesky r (d l))

def blockCorrection {n B T : ℕ} {uc : ℝ} (r : Arithmetic uc)
    (ι : Fin n ≃ Fin B × Fin T) (d : Fin B → Mat T) (rhs : Vec n) : Vec n :=
  fun i => choleskySolve r (cholesky r (d (ι i).1))
    (fun j => rhs (ι.symm ((ι i).1, j))) (ι i).2

def residual {n : ℕ} {us : ℝ} (r : Arithmetic us) (S : ℕ)
    (A : Mat n) (b v : Vec n) : Vec n :=
  fun i => r.sub (b i) (tiledMatVec r S A v i)

def correction {n B T : ℕ} {us uc : ℝ}
    (rs : Arithmetic us) (rc : Arithmetic uc) (cv : Conversion uc)
    (ι : Fin n ≃ Fin B × Fin T) (S : ℕ) (d : Fin B → Mat T)
    (A : Mat n) (b v : Vec n) : Vec n :=
  blockCorrection rc ι d (fun i => cv.apply (residual rs S A b v i))

def jacobiStep {n B T : ℕ} {us uc : ℝ}
    (rs : Arithmetic us) (rc : Arithmetic uc) (cv : Conversion uc)
    (ι : Fin n ≃ Fin B × Fin T) (S : ℕ) (d : Fin B → Mat T)
    (A : Mat n) (b v : Vec n) : Vec n :=
  fun i => rs.add (v i) (correction rs rc cv ι S d A b v i)

/-- The computed iterates, from an arbitrary initial guess. -/
def iterates {n B T : ℕ} {us uc : ℝ}
    (rs : Arithmetic us) (rc : Arithmetic uc) (cv : Conversion uc)
    (ι : Fin n ≃ Fin B × Fin T) (S : ℕ) (d : Fin B → Mat T)
    (A : Mat n) (b initial : Vec n) : ℕ → Vec n
  | 0 => initial
  | k + 1 => jacobiStep rs rc cv ι S d A b (iterates rs rc cv ι S d A b initial k)

def error {n : ℕ} (v : ℕ → Vec n) (x : Vec n) (k : ℕ) : Vec n := v k - x

/-- Source G, using the genuine inverse of the assembled SPD block matrix. -/
def G {n : ℕ} (T : ℕ) (uc : ℝ) (D Rhat : Mat n) : Mat n :=
  c₂ T uc • (matrixAbs D⁻¹ * matrixAbs Rhat.transpose * matrixAbs Rhat)

def eta {n : ℕ} (T : ℕ) (uc : ℝ) (D Rhat : Mat n) : ℝ :=
  matrixInf (G T uc D Rhat)

def q {n : ℕ} (D N : Mat n) : ℝ := matrixInf (D⁻¹ * N)

def p {n : ℕ} (D A : Mat n) : ℝ := matrixInf (matrixAbs D⁻¹ * matrixAbs A)

def alpha {n : ℕ} (T S : ℕ) (us uc : ℝ) (D N A Rhat : Mat n) : ℝ :=
  (eta T uc D Rhat + us + (1 + us) * (q D N + uc * p D A)) /
      (1 - eta T uc D Rhat) + us +
    (1 + us) * (1 + uc) * c₁ n S us * p D A / (1 - eta T uc D Rhat)

def beta {n : ℕ} (T S : ℕ) (us uc : ℝ) (D A Rhat : Mat n) (x b : Vec n) : ℝ :=
  (us + (1 + us) * (1 + uc) * c₁ n S us * p D A / (1 - eta T uc D Rhat)) *
      vectorInf x +
    (1 + us) * (1 + uc) * us / (1 - eta T uc D Rhat) * matrixInf D⁻¹ * vectorInf b

lemma vectorInf_nonneg {n : ℕ} (v : Vec n) : 0 ≤ vectorInf v := by
  exact NNReal.coe_nonneg _

lemma matrixInf_nonneg {n : ℕ} (A : Mat n) : 0 ≤ matrixInf A := by
  exact NNReal.coe_nonneg _

lemma abs_le_vectorInf {n : ℕ} (v : Vec n) (i : Fin n) : |v i| ≤ vectorInf v := by
  unfold vectorInf
  have h := Finset.le_sup (f := fun j => Real.toNNReal |v j|) (Finset.mem_univ i)
  have h' := (NNReal.coe_le_coe).mpr h
  simpa only [Real.coe_toNNReal _ (abs_nonneg _)] using h' 

lemma rowSum_le_matrixInf {n : ℕ} (A : Mat n) (i : Fin n) :
    (∑ j, |A i j|) ≤ matrixInf A := by
  unfold matrixInf
  have h := Finset.le_sup (f := fun k => Real.toNNReal (∑ j, |A k j|))
    (Finset.mem_univ i)
  have h' := (NNReal.coe_le_coe).mpr h
  simpa only [Real.coe_toNNReal _ (Finset.sum_nonneg (fun j _ => abs_nonneg _))] using h'

lemma vectorInf_le {n : ℕ} (v : Vec n) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, |v i| ≤ c) : vectorInf v ≤ c := by
  unfold vectorInf
  have h' : Finset.univ.sup (fun i => Real.toNNReal |v i|) ≤ Real.toNNReal c := by
    exact Finset.sup_le (fun i _ => Real.toNNReal_le_toNNReal (h i))
  have h'' : ((Finset.univ.sup (fun i => Real.toNNReal |v i|) : NNReal) : ℝ) ≤
      (Real.toNNReal c : ℝ) := by exact_mod_cast h'
  simpa only [Real.coe_toNNReal c hc] using h''

lemma vectorInf_add_le {n : ℕ} (v w : Vec n) :
    vectorInf (v + w) ≤ vectorInf v + vectorInf w := by
  apply vectorInf_le _ (add_nonneg (vectorInf_nonneg _) (vectorInf_nonneg _))
  intro i
  exact (abs_add_le _ _).trans (add_le_add (abs_le_vectorInf v i) (abs_le_vectorInf w i))

lemma vectorInf_mulVec_le {n : ℕ} (A : Mat n) (v : Vec n) :
    vectorInf (A.mulVec v) ≤ matrixInf A * vectorInf v := by
  apply vectorInf_le _ (mul_nonneg (matrixInf_nonneg _) (vectorInf_nonneg _))
  intro i
  calc
    |A.mulVec v i| ≤ ∑ j, |A i j * v j| := by
      simpa only [Matrix.mulVec, dotProduct] using
        Finset.abs_sum_le_sum_abs (fun j => A i j * v j) Finset.univ
    _ = ∑ j, |A i j| * |v j| := by simp only [abs_mul]
    _ ≤ ∑ j, |A i j| * vectorInf v := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (abs_le_vectorInf v j) (abs_nonneg _)
    _ = (∑ j, |A i j|) * vectorInf v := (Finset.sum_mul ..).symm
    _ ≤ matrixInf A * vectorInf v :=
      mul_le_mul_of_nonneg_right (rowSum_le_matrixInf A i) (vectorInf_nonneg _)

lemma matrixInf_le {n : ℕ} (A : Mat n) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, (∑ j, |A i j|) ≤ c) : matrixInf A ≤ c := by
  unfold matrixInf
  have h' : Finset.univ.sup (fun i => Real.toNNReal (∑ j, |A i j|)) ≤
      Real.toNNReal c := by
    exact Finset.sup_le (fun i _ => Real.toNNReal_le_toNNReal (h i))
  have h'' := (NNReal.coe_le_coe).mpr h'
  simpa only [Real.coe_toNNReal c hc] using h''

lemma matrixInf_mul_le {n : ℕ} (A B : Mat n) :
    matrixInf (A * B) ≤ matrixInf A * matrixInf B := by
  apply matrixInf_le _ (mul_nonneg (matrixInf_nonneg _) (matrixInf_nonneg _))
  intro i
  calc
    ∑ j, |(A * B) i j| ≤ ∑ j, ∑ k, |A i k| * |B k j| := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Matrix.mul_apply, abs_mul] using
        Finset.abs_sum_le_sum_abs (fun k => A i k * B k j) Finset.univ
    _ = ∑ k, |A i k| * ∑ j, |B k j| := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ k, |A i k| * matrixInf B := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (rowSum_le_matrixInf B k) (abs_nonneg _)
    _ = (∑ k, |A i k|) * matrixInf B := (Finset.sum_mul ..).symm
    _ ≤ matrixInf A * matrixInf B :=
      mul_le_mul_of_nonneg_right (rowSum_le_matrixInf A i) (matrixInf_nonneg _)

lemma gamma_nonneg {m : ℕ} {u : ℝ} (hu : 0 ≤ u) (hmu : (m : ℝ) * u < 1) :
    0 ≤ gamma m u := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (sub_pos.mpr hmu).le

lemma c₁_nonneg {n S : ℕ} {us : ℝ} (hus : 0 ≤ us)
    (hgamma : ((S + n / S - 1 : ℕ) : ℝ) * us < 1) : 0 ≤ c₁ n S us := by
  unfold c₁
  positivity [gamma_nonneg hus hgamma]

lemma c₂_nonneg {T : ℕ} {uc : ℝ} (huc : 0 ≤ uc)
    (hgamma : ((T + 1 : ℕ) : ℝ) * uc < 1) : 0 ≤ c₂ T uc := by
  unfold c₂
  positivity [gamma_nonneg huc hgamma]

lemma alpha_nonneg {n T S : ℕ} {us uc : ℝ} (D N A Rhat : Mat n)
    (hus : 0 ≤ us) (huc : 0 ≤ uc)
    (hgamma : ((S + n / S - 1 : ℕ) : ℝ) * us < 1)
    (heta : eta T uc D Rhat < 1) : 0 ≤ alpha T S us uc D N A Rhat := by
  have he : 0 ≤ eta T uc D Rhat := matrixInf_nonneg _
  have hq : 0 ≤ q D N := matrixInf_nonneg _
  have hp : 0 ≤ p D A := matrixInf_nonneg _
  have hc := c₁_nonneg hus hgamma
  have hd := sub_pos.mpr heta
  unfold alpha
  positivity

lemma RelativeError.abs_error {u exact computed : ℝ}
    (h : RelativeError u exact computed) : |computed - exact| ≤ u * |exact| := by
  obtain ⟨δ, hδ, rfl⟩ := h
  calc
    |exact * (1 + δ) - exact| = |δ| * |exact| := by
      rw [show exact * (1 + δ) - exact = δ * exact by ring, abs_mul]
    _ ≤ u * |exact| := mul_le_mul_of_nonneg_right hδ (abs_nonneg _)

lemma RelativeError.abs_computed {u exact computed : ℝ}
    (h : RelativeError u exact computed) : |computed| ≤ (1 + u) * |exact| := by
  calc
    |computed| = |(computed - exact) + exact| := by congr 1; ring
    _ ≤ |computed - exact| + |exact| := abs_add_le _ _
    _ ≤ u * |exact| + |exact| := by gcongr; exact h.abs_error
    _ = (1 + u) * |exact| := by ring

/-- Split the rounded residual into the source's right-hand-side and
matrix-vector contributions, retaining the exact c1 coefficient. -/
lemma rounded_residual_split {u g w : ℝ} (r : Arithmetic u) (b z y : ℝ)
    (hu : 0 ≤ u) (hg : 0 ≤ g) (hw : 0 ≤ w)
    (hy : |y| ≤ w) (hz : |z - y| ≤ g * w) :
    ∃ db dz : ℝ, r.sub b z = b - y + db + dz ∧
      |db| ≤ u * |b| ∧ |dz| ≤ (g + u + u * g) * w := by
  obtain ⟨δ, hδ, hsub⟩ := r.sub_model b z
  refine ⟨δ * b, -(z - y) * (1 + δ) - δ * y, ?_, ?_, ?_⟩
  · rw [hsub]; ring
  · simpa only [abs_mul] using mul_le_mul_of_nonneg_right hδ (abs_nonneg b)
  · have hδ1 : |1 + δ| ≤ 1 + u := by
      calc
        |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
        _ ≤ 1 + u := by simpa using add_le_add_left hδ 1
    calc
      |-(z - y) * (1 + δ) - δ * y| ≤
          |-(z - y) * (1 + δ)| + |δ * y| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (-(z - y) * (1 + δ)) (-(δ * y))
      _ = |z - y| * |1 + δ| + |δ| * |y| := by rw [abs_mul, abs_neg, abs_mul]
      _ ≤ (g * w) * (1 + u) + u * w := by gcongr
      _ = (g + u + u * g) * w := by ring

lemma affine_recurrence_bound {a z : ℝ} (f : ℕ → ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (hstep : ∀ k, f (k + 1) ≤ a * f k + z) :
    ∀ k, f k ≤ a ^ k * f 0 + (1 - a ^ k) / (1 - a) * z := by
  have hd : 1 - a ≠ 0 := ne_of_gt (sub_pos.mpr ha1)
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      f (k + 1) ≤ a * f k + z := hstep k
      _ ≤ a * (a ^ k * f 0 + (1 - a ^ k) / (1 - a) * z) + z := by
        gcongr
      _ = a ^ (k + 1) * f 0 + (1 - a ^ (k + 1)) / (1 - a) * z := by
        rw [pow_succ]
        field_simp
        ring

lemma affine_recurrence_limsup {a z : ℝ} (f : ℕ → ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (hf : ∀ k, 0 ≤ f k) (hstep : ∀ k, f (k + 1) ≤ a * f k + z) :
    Filter.limsup f Filter.atTop ≤ z / (1 - a) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one ha ha1
  have hlim : Filter.Tendsto
      (fun k : ℕ => a ^ k * f 0 + (1 - a ^ k) / (1 - a) * z)
      Filter.atTop (nhds (z / (1 - a))) := by
    convert (hpow.mul_const (f 0)).add
      (((tendsto_const_nhds.sub hpow).div_const (1 - a)).mul_const z) using 1
    all_goals simp [div_eq_mul_inv, mul_comm]
  have hc : Filter.atTop.IsCoboundedUnder (· ≤ ·) f := by
    exact Filter.isCoboundedUnder_le_of_le Filter.atTop hf
  calc
    Filter.limsup f Filter.atTop ≤ Filter.limsup
        (fun k : ℕ => a ^ k * f 0 + (1 - a ^ k) / (1 - a) * z) Filter.atTop :=
      Filter.limsup_le_limsup
        (Filter.Eventually.of_forall (affine_recurrence_bound f ha ha1 hstep))
        hc hlim.isBoundedUnder_le
    _ = z / (1 - a) := hlim.limsup_eq

/-- Monotonicity of the maximum norm under componentwise absolute bounds. -/
lemma vectorInf_mono {n : ℕ} (v w : Vec n) (h : ∀ i, |v i| ≤ |w i|) :
    vectorInf v ≤ vectorInf w := by
  exact vectorInf_le v (vectorInf_nonneg w) (fun i => (h i).trans (abs_le_vectorInf w i))

lemma vectorInf_neg {n : ℕ} (v : Vec n) : vectorInf (-v) = vectorInf v := by
  unfold vectorInf
  simp

lemma vectorInf_sub_le {n : ℕ} (v w : Vec n) :
    vectorInf (v - w) ≤ vectorInf v + vectorInf w := by
  simpa only [sub_eq_add_neg, vectorInf_neg] using vectorInf_add_le v (-w)

/-- Absolute matrix-vector multiplication retains the combined majorant matrix. -/
lemma abs_mulVec_le {n : ℕ} (A : Mat n) (v : Vec n) (i : Fin n) :
    |A.mulVec v i| ≤ (matrixAbs A).mulVec (fun j => |v j|) i := by
  simpa only [Matrix.mulVec, dotProduct, matrixAbs, abs_mul] using
    Finset.abs_sum_le_sum_abs (fun j => A i j * v j) Finset.univ

lemma matrixAbs_mulVec_nonneg {n : ℕ} (A : Mat n) (v : Vec n)
    (hv : ∀ i, 0 ≤ v i) (i : Fin n) : 0 ≤ (matrixAbs A).mulVec v i := by
  unfold Matrix.mulVec dotProduct matrixAbs
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hv j))

/-- A componentwise error majorant can be multiplied by an inverse without
replacing the norm of the combined majorant by a product of matrix norms. -/
lemma vectorInf_mulVec_majorant {n : ℕ} (M H : Mat n) (v w : Vec n)
    (h : ∀ i, |v i| ≤ H.mulVec w i) :
    vectorInf (M.mulVec v) ≤ matrixInf (matrixAbs M * H) * vectorInf w := by
  have hcomponent : ∀ i, |M.mulVec v i| ≤ (matrixAbs M * H).mulVec w i := by
    intro i
    calc
      |M.mulVec v i| ≤ (matrixAbs M).mulVec (fun j => |v j|) i := abs_mulVec_le M v i
      _ ≤ (matrixAbs M).mulVec (H.mulVec w) i := by
        unfold Matrix.mulVec dotProduct matrixAbs
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (h j) (abs_nonneg _)
      _ = (matrixAbs M * H).mulVec w i := by rw [Matrix.mulVec_mulVec]
  calc
    vectorInf (M.mulVec v) ≤ vectorInf ((matrixAbs M * H).mulVec w) := by
      apply vectorInf_mono
      intro i
      exact (hcomponent i).trans (le_abs_self _)
    _ ≤ matrixInf (matrixAbs M * H) * vectorInf w := vectorInf_mulVec_le _ _

lemma matrixAbs_mul_le {n : ℕ} (A B : Mat n) (i j : Fin n) :
    |(A * B) i j| ≤ (matrixAbs A * matrixAbs B) i j := by
  simpa only [Matrix.mul_apply, matrixAbs, abs_mul] using
    Finset.abs_sum_le_sum_abs (fun k => A i k * B k j) Finset.univ

/-- Direct absorption of the correction norm uses only eta < 1. -/
lemma correction_norm_absorb {C E F e q₀ uc p₀ : ℝ}
    (he : e < 1)
    (h : C ≤ (1 + q₀ + uc * p₀) * E + F + e * C) :
    C ≤ ((1 + q₀ + uc * p₀) * E + F) / (1 - e) := by
  apply (le_div_iff₀ (sub_pos.mpr he)).mpr
  nlinarith [h]

/-- The exact rational coefficient identity in the update estimate. -/
lemma update_coefficient_identity (e s Q E F X : ℝ) (he : e ≠ 1) :
    Q * E + F + s * X + (e + s) * (((1 + Q) * E + F) / (1 - e)) =
      ((e + s + (1 + s) * Q) / (1 - e)) * E +
        s * X + (1 + s) * F / (1 - e) := by
  have hd : 1 - e ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
  field_simp
  ring

/-- Combine the correction and update norm estimates, with exactly the source
coefficients. This lemma does not postulate either estimate for an execution. -/
lemma one_step_norm_algebra {E E' C X Xstar B₀ e q₀ p₀ s t c : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hc : 0 ≤ c) (hp : 0 ≤ p₀)
    (he0 : 0 ≤ e) (he : e < 1)
    (hX : X ≤ Xstar + E)
    (hC : C ≤ (1 + q₀ + t * p₀) * E +
      (1 + t) * (s * B₀ + c * p₀ * X) + e * C)
    (hupdate : E' ≤ (q₀ + t * p₀) * E +
      (1 + t) * (s * B₀ + c * p₀ * X) + s * X + (e + s) * C) :
    E' ≤ ((e + s + (1 + s) * (q₀ + t * p₀)) / (1 - e) + s +
        (1 + s) * (1 + t) * c * p₀ / (1 - e)) * E +
      (s + (1 + s) * (1 + t) * c * p₀ / (1 - e)) * Xstar +
      (1 + s) * (1 + t) * s / (1 - e) * B₀ := by
  have hd := sub_pos.mpr he
  have hC' := correction_norm_absorb he hC
  have hscale : 0 ≤ e + s := add_nonneg he0 hs
  have hcoef : 0 ≤ s + (1 + s) * (1 + t) * c * p₀ / (1 - e) := by positivity
  calc
    E' ≤ (q₀ + t * p₀) * E + (1 + t) * (s * B₀ + c * p₀ * X) + s * X +
        (e + s) * (((1 + q₀ + t * p₀) * E +
          (1 + t) * (s * B₀ + c * p₀ * X)) / (1 - e)) := by
      exact hupdate.trans (add_le_add_right (mul_le_mul_of_nonneg_left hC' hscale) _)
    _ = ((e + s + (1 + s) * (q₀ + t * p₀)) / (1 - e)) * E +
        (s + (1 + s) * (1 + t) * c * p₀ / (1 - e)) * X +
        (1 + s) * (1 + t) * s / (1 - e) * B₀ := by
      field_simp
      ring
    _ ≤ ((e + s + (1 + s) * (q₀ + t * p₀)) / (1 - e)) * E +
        (s + (1 + s) * (1 + t) * c * p₀ / (1 - e)) * (Xstar + E) +
        (1 + s) * (1 + t) * s / (1 - e) * B₀ := by
      gcongr
    _ = _ := by ring

lemma gamma_mono {m k : ℕ} {u : ℝ} (hu : 0 ≤ u) (hmk : m ≤ k)
    (hk : (k : ℝ) * u < 1) : gamma m u ≤ gamma k u := by
  have hmul : (m : ℝ) * u ≤ (k : ℝ) * u := by exact_mod_cast mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmk) hu
  have hm : 0 < 1 - (m : ℝ) * u := by linarith
  have hk' : 0 < 1 - (k : ℝ) * u := by linarith
  unfold gamma
  apply (div_le_div_iff₀ hm hk').mpr
  nlinarith

lemma gamma_step {m : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (hm : ((m + 1 : ℕ) : ℝ) * u < 1) :
    gamma m u * (1 + u) + u ≤ gamma (m + 1) u := by
  have hm' : (m : ℝ) * u < 1 := by
    push_cast at hm
    nlinarith
  have hd : 0 < 1 - (m : ℝ) * u := sub_pos.mpr hm'
  have hd' : 0 < 1 - ((m + 1 : ℕ) : ℝ) * u := sub_pos.mpr hm
  unfold gamma
  apply (le_div_iff₀ hd').mpr
  apply (mul_le_mul_iff_left₀ hd).mp
  field_simp
  push_cast
  nlinarith [sq_nonneg u]

/-- Forward error of sequential accumulation with a supplied first accumulator.
The number of rounded additions, rather than the number of terms, controls gamma. -/
lemma rounded_foldl_error {u : ℝ} (r : Arithmetic u) (hu : 0 ≤ u)
    (as : List ℝ) (a : ℝ) (hgamma : (as.length : ℝ) * u < 1) :
    |as.foldl r.add a - (a + as.sum)| ≤
      gamma as.length u * (|a| + (as.map abs).sum) := by
  induction as generalizing a with
  | nil => simp [gamma]
  | cons b bs ih =>
    have hlen : (bs.length : ℝ) * u < 1 := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hgamma
      nlinarith
    have hg0 := gamma_nonneg hu hlen
    have hg1 := gamma_nonneg hu hgamma
    have hgmono := gamma_mono hu (Nat.le_succ bs.length) hgamma
    have hgstep := gamma_step hu hgamma
    have hadd := (r.add_model a b).abs_error
    have habs : |r.add a b| ≤ (1 + u) * (|a| + |b|) := by
      exact (r.add_model a b).abs_computed.trans
        (mul_le_mul_of_nonneg_left (abs_add_le a b) (by positivity))
    have hsum0 : 0 ≤ (bs.map abs).sum := List.sum_nonneg (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact abs_nonneg y)
    calc
      |(b :: bs).foldl r.add a - (a + (b :: bs).sum)| =
          |(bs.foldl r.add (r.add a b) - (r.add a b + bs.sum)) +
            (r.add a b - (a + b))| := by
        simp only [List.foldl_cons, List.sum_cons]
        congr 1
        ring
      _ ≤ |bs.foldl r.add (r.add a b) - (r.add a b + bs.sum)| +
          |r.add a b - (a + b)| := abs_add_le _ _
      _ ≤ gamma bs.length u * (|r.add a b| + (bs.map abs).sum) + u * |a + b| :=
        add_le_add (ih (r.add a b) hlen) hadd
      _ ≤ gamma bs.length u * ((1 + u) * (|a| + |b|) + (bs.map abs).sum) +
          u * (|a| + |b|) := by gcongr; exact abs_add_le a b
      _ = (gamma bs.length u * (1 + u) + u) * (|a| + |b|) +
          gamma bs.length u * (bs.map abs).sum := by ring
      _ ≤ gamma (bs.length + 1) u * (|a| + |b|) +
          gamma (bs.length + 1) u * (bs.map abs).sum := by gcongr
      _ = gamma (b :: bs).length u * (|a| + ((b :: bs).map abs).sum) := by
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        ring

lemma roundedSum_error {u : ℝ} (r : Arithmetic u) (hu : 0 ≤ u)
    (as : List ℝ) (hgamma : ((as.length - 1 : ℕ) : ℝ) * u < 1) :
    |roundedSum r as - as.sum| ≤ gamma (as.length - 1) u * (as.map abs).sum := by
  cases as with
  | nil => simp [roundedSum, gamma]
  | cons a as =>
    simpa only [roundedSum, List.length_cons, Nat.add_sub_cancel,
      List.sum_cons, List.map_cons] using rounded_foldl_error r hu as a hgamma

/-- Sum of pointwise absolute error bounds, for lists with repetitions allowed. -/
lemma list_sum_error {I : Type*} (indices : List I) (f g : I → ℝ) (c : ℝ)
    (h : ∀ i ∈ indices, |f i - g i| ≤ c * |g i|) :
    |(indices.map f).sum - (indices.map g).sum| ≤
      c * (indices.map (fun i => |g i|)).sum := by
  induction indices with
  | nil => simp
  | cons i indices ih =>
    simp only [List.map_cons, List.sum_cons]
    calc
      |f i + (indices.map f).sum - (g i + (indices.map g).sum)| =
          |(f i - g i) + ((indices.map f).sum - (indices.map g).sum)| := by
        congr 1; ring
      _ ≤ |f i - g i| + |(indices.map f).sum - (indices.map g).sum| := abs_add_le _ _
      _ ≤ c * |g i| + c * (indices.map (fun i => |g i|)).sum :=
        add_le_add (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))
      _ = _ := by ring

/-- Dot-product error derived from the actual rounded products and additions. -/
lemma roundedDot_error {I : Type*} {u : ℝ} (r : Arithmetic u) (hu : 0 ≤ u)
    (indices : List I) (a b : I → ℝ)
    (hgamma : (indices.length : ℝ) * u < 1) :
    |roundedDot r indices a b - (indices.map (fun i => a i * b i)).sum| ≤
      gamma indices.length u * (indices.map (fun i => |a i * b i|)).sum := by
  cases indices with
  | nil => simp [roundedDot, roundedSum, gamma]
  | cons i indices =>
    let l := i :: indices
    let W := (l.map (fun i => |a i * b i|)).sum
    have hlen : ((l.length - 1 : ℕ) : ℝ) * u < 1 := by
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le _ _)) hu) hgamma
    have hg0 := gamma_nonneg hu hlen
    have hprod : |(l.map (fun i => r.mul (a i) (b i))).sum -
        (l.map (fun i => a i * b i)).sum| ≤ u * W :=
      list_sum_error l _ _ u (fun j _ => (r.mul_model (a j) (b j)).abs_error)
    have hW : ((l.map (fun i => r.mul (a i) (b i))).map abs).sum ≤ (1 + u) * W := by
      simp only [List.map_map]
      calc
        (l.map (fun i => |r.mul (a i) (b i)|)).sum ≤
            (l.map (fun i => (1 + u) * |a i * b i|)).sum :=
          List.sum_le_sum (fun j _ => (r.mul_model (a j) (b j)).abs_computed)
        _ = (1 + u) * W := List.sum_map_mul_left _ _ _
    have hW0 : 0 ≤ W := List.sum_nonneg (fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      exact abs_nonneg _)
    have hstep : gamma (l.length - 1) u * (1 + u) + u ≤ gamma l.length u := by
      simpa only [l, List.length_cons, Nat.add_sub_cancel] using
        (gamma_step (m := indices.length) hu hgamma)
    calc
      |roundedDot r l a b - (l.map (fun i => a i * b i)).sum| =
          |(roundedDot r l a b - (l.map (fun i => r.mul (a i) (b i))).sum) +
            ((l.map (fun i => r.mul (a i) (b i))).sum -
              (l.map (fun i => a i * b i)).sum)| := by congr 1; ring
      _ ≤ |roundedDot r l a b - (l.map (fun i => r.mul (a i) (b i))).sum| +
            |(l.map (fun i => r.mul (a i) (b i))).sum -
              (l.map (fun i => a i * b i)).sum| := abs_add_le _ _
      _ ≤ gamma (l.length - 1) u *
            ((l.map (fun i => r.mul (a i) (b i))).map abs).sum + u * W := by
        exact add_le_add (by
          simpa only [roundedDot, List.length_map] using
            roundedSum_error r hu (l.map (fun i => r.mul (a i) (b i)))
              (by simpa only [List.length_map] using hlen)) hprod
      _ ≤ gamma (l.length - 1) u * ((1 + u) * W) + u * W := by gcongr
      _ = (gamma (l.length - 1) u * (1 + u) + u) * W := by ring
      _ ≤ gamma l.length u * W := mul_le_mul_of_nonneg_right hstep hW0

lemma gamma_add {m k : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (hmk : ((m + k : ℕ) : ℝ) * u < 1) :
    gamma m u + gamma k u + gamma m u * gamma k u ≤ gamma (m + k) u := by
  have hm : (m : ℝ) * u < 1 := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_add_right m k)) hu) hmk
  have hk : (k : ℝ) * u < 1 := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_add_left k m)) hu) hmk
  have hdm := sub_pos.mpr hm
  have hdk := sub_pos.mpr hk
  have hdmk := sub_pos.mpr hmk
  have hone : ∀ j : ℕ, (j : ℝ) * u < 1 →
      1 + gamma j u = 1 / (1 - (j : ℝ) * u) := by
    intro j hj
    unfold gamma
    field_simp [ne_of_gt (sub_pos.mpr hj)]
    ring
  have hden : 0 < (1 - (m : ℝ) * u) * (1 - (k : ℝ) * u) := mul_pos hdm hdk
  have hbound : 1 / ((1 - (m : ℝ) * u) * (1 - (k : ℝ) * u)) ≤
      1 / (1 - ((m + k : ℕ) : ℝ) * u) := by
    apply (div_le_div_iff₀ hden hdmk).mpr
    push_cast
    nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg k)) (sq_nonneg u)]
  have hprod : (1 + gamma m u) * (1 + gamma k u) ≤ 1 + gamma (m + k) u := by
    rw [hone m hm, hone k hk, hone (m + k) hmk, one_div_mul_one_div]
    exact hbound
  nlinarith [hprod]

/-- An elementary relative error can be expressed relative to the computed value
when u < 1. This is the inverse-factor bound used in substitution. -/
lemma RelativeError.abs_error_computed {u exact computed : ℝ}
    (h : RelativeError u exact computed) (hu : 0 ≤ u) (hu1 : u < 1) :
    |exact - computed| ≤ gamma 1 u * |computed| := by
  have h₀ : |exact - computed| ≤ u * |exact| := by
    simpa only [abs_sub_comm] using h.abs_error
  have hexact : |exact| ≤ |exact - computed| + |computed| := by
    calc
      |exact| = |(exact - computed) + computed| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have h₁ := mul_le_mul_of_nonneg_left hexact hu
  have hd : 0 < 1 - u := sub_pos.mpr hu1
  have h₂ : |exact - computed| ≤ u * |computed| / (1 - u) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  simpa [gamma, div_mul_eq_mul_div] using h₂

/-- The residual of a rounded division, with a nonzero divisor. -/
lemma rounded_division_residual {u : ℝ} (r : Arithmetic u) (a b : ℝ)
    (hb : b ≠ 0) (hu : 0 ≤ u) (hu1 : u < 1) :
    |a - b * r.div a b| ≤ gamma 1 u * |b * r.div a b| := by
  have h := (r.div_model a b hb).abs_error_computed hu hu1
  have hmul := mul_le_mul_of_nonneg_left h (abs_nonneg b)
  calc
    |a - b * r.div a b| = |b| * |a / b - r.div a b| := by
      rw [← abs_mul]
      congr 1
      field_simp
    _ ≤ |b| * (gamma 1 u * |r.div a b|) := hmul
    _ = gamma 1 u * |b * r.div a b| := by rw [abs_mul]; ring

/-- Split the actual rounded solution addition into its two source terms. -/
lemma rounded_update_split {u : ℝ} (r : Arithmetic u) (a b : ℝ) :
    ∃ da db : ℝ, r.add a b = a + b + da + db ∧
      |da| ≤ u * |a| ∧ |db| ≤ u * |b| := by
  obtain ⟨δ, hδ, hround⟩ := r.add_model a b
  refine ⟨a * δ, b * δ, ?_, ?_, ?_⟩
  · rw [hround]; ring
  · rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
  · rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)

/-- A computed square root supplies a two-factor diagonal residual bound. -/
lemma rounded_sqrt_residual {u : ℝ} (r : Arithmetic u) (a : ℝ)
    (ha : 0 ≤ a) (hu : 0 ≤ u) (hgamma : (2 : ℝ) * u < 1) :
    |a - (r.sqrt a) ^ 2| ≤ gamma 2 u * |(r.sqrt a) ^ 2| := by
  have hu1 : u < 1 := by linarith
  have hg1 := gamma_nonneg (m := 1) hu (by simpa using hu1)
  have h := (r.sqrt_model a ha).abs_error_computed hu hu1
  have hs : |Real.sqrt a| ≤ (1 + gamma 1 u) * |r.sqrt a| := by
    calc
      |Real.sqrt a| ≤ |Real.sqrt a - r.sqrt a| + |r.sqrt a| := by
        calc
          |Real.sqrt a| = |(Real.sqrt a - r.sqrt a) + r.sqrt a| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      _ ≤ gamma 1 u * |r.sqrt a| + |r.sqrt a| := add_le_add h le_rfl
      _ = _ := by ring
  have hfactor : |Real.sqrt a + r.sqrt a| ≤ (2 + gamma 1 u) * |r.sqrt a| := by
    calc
      |Real.sqrt a + r.sqrt a| ≤ |Real.sqrt a| + |r.sqrt a| := abs_add_le _ _
      _ ≤ (1 + gamma 1 u) * |r.sqrt a| + |r.sqrt a| := add_le_add hs le_rfl
      _ = _ := by ring
  have hcoef : gamma 1 u * (2 + gamma 1 u) ≤ gamma 2 u := by
    have hγ := gamma_add (m := 1) (k := 1) hu (by simpa using hgamma)
    nlinarith
  calc
    |a - (r.sqrt a) ^ 2| = |Real.sqrt a - r.sqrt a| * |Real.sqrt a + r.sqrt a| := by
      rw [← abs_mul]
      congr 1
      nlinarith [Real.sq_sqrt ha]
    _ ≤ (gamma 1 u * |r.sqrt a|) * ((2 + gamma 1 u) * |r.sqrt a|) := by
      gcongr
    _ = (gamma 1 u * (2 + gamma 1 u)) * |(r.sqrt a) ^ 2| := by
      rw [abs_pow]
      ring
    _ ≤ gamma 2 u * |(r.sqrt a) ^ 2| := mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)

/-- Backward residual of one implemented triangular row. The dot product and
subtraction are evaluated exactly as in `subtractDot`; no solve estimate is assumed. -/
lemma triangular_row_residual {I : Type*} {u : ℝ} (r : Arithmetic u)
    (indices : List I) (a b : I → ℝ) (c diag : ℝ) (T : ℕ)
    (hu : 0 ≤ u) (hT : indices.length < T)
    (hgamma : (T : ℝ) * u < 1) (hdiag : diag ≠ 0) :
    let y := r.div (subtractDot r indices c a b) diag
    |c - ((indices.map (fun i => a i * b i)).sum + diag * y)| ≤
      gamma T u * ((indices.map (fun i => |a i * b i|)).sum + |diag * y|) := by
  have h1T : 1 ≤ T := by omega
  have hgamma1 : (1 : ℝ) * u < 1 := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast h1T) hu) hgamma
  have hu1 : u < 1 := by simpa using hgamma1
  have hg1 := gamma_nonneg (m := 1) hu (by simpa using hu1)
  have hmono1 := gamma_mono hu h1T hgamma
  cases indices with
  | nil =>
    simp only [subtractDot, List.map_nil, List.sum_nil, zero_add]
    exact (rounded_division_residual r c diag hdiag hu hu1).trans
      (mul_le_mul_of_nonneg_right hmono1 (abs_nonneg _))
  | cons i indices =>
    let l := i :: indices
    let dot := roundedDot r l a b
    let f := r.sub c dot
    let y := r.div f diag
    let S₀ := (l.map (fun i => a i * b i)).sum
    let W := (l.map (fun i => |a i * b i|)).sum
    change |c - (S₀ + diag * y)| ≤ gamma T u * (W + |diag * y|)
    have hlen : (l.length : ℝ) * u < 1 := lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_of_lt hT)) hu) hgamma
    have hmono := gamma_mono hu (Nat.le_of_lt hT) hgamma
    have h2T : 2 ≤ T := by simp only [List.length_cons] at hT; omega
    have hmono2 := gamma_mono hu h2T hgamma
    have hgamma2 : (2 : ℝ) * u < 1 := lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by exact_mod_cast h2T) hu) hgamma
    have hcoef : gamma 1 u * (1 + gamma 1 u) + gamma 1 u ≤ gamma T u := by
      have hg := gamma_add (m := 1) (k := 1) hu (by simpa using hgamma2)
      nlinarith
    have hdot : |dot - S₀| ≤ gamma l.length u * W := roundedDot_error r hu l a b hlen
    have hsub : |c - dot - f| ≤ gamma 1 u * |f| :=
      (r.sub_model c dot).abs_error_computed hu hu1
    have hdiv : |f - diag * y| ≤ gamma 1 u * |diag * y| :=
      rounded_division_residual r f diag hdiag hu hu1
    have hf : |f| ≤ (1 + gamma 1 u) * |diag * y| := by
      calc
        |f| = |(f - diag * y) + diag * y| := by congr 1; ring
        _ ≤ |f - diag * y| + |diag * y| := abs_add_le _ _
        _ ≤ gamma 1 u * |diag * y| + |diag * y| := add_le_add hdiv le_rfl
        _ = _ := by ring
    have hW0 : 0 ≤ W := List.sum_nonneg (fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      exact abs_nonneg _)
    calc
      |c - (S₀ + diag * y)| = |(dot - S₀) + (c - dot - f) + (f - diag * y)| := by
        congr 1; ring
      _ ≤ |dot - S₀| + |c - dot - f| + |f - diag * y| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ gamma l.length u * W + gamma 1 u * |f| + gamma 1 u * |diag * y| :=
        add_le_add (add_le_add hdot hsub) hdiv
      _ ≤ gamma l.length u * W + gamma 1 u * ((1 + gamma 1 u) * |diag * y|) +
          gamma 1 u * |diag * y| := by gcongr
      _ = gamma l.length u * W +
          (gamma 1 u * (1 + gamma 1 u) + gamma 1 u) * |diag * y| := by ring
      _ ≤ gamma T u * W + gamma T u * |diag * y| :=
        add_le_add (mul_le_mul_of_nonneg_right hmono hW0)
          (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _))
      _ = _ := by ring

/-- Local backward error of an implemented Cholesky diagonal, including the
rounded square root and the omitted subtraction in the first row. -/
lemma cholesky_diagonal_residual {I : Type*} {u : ℝ} (r : Arithmetic u)
    (indices : List I) (a : I → ℝ) (c : ℝ) (T : ℕ)
    (hu : 0 ≤ u) (hT : indices.length < T)
    (hgamma : ((T + 1 : ℕ) : ℝ) * u < 1)
    (hrad : 0 ≤ subtractDot r indices c a a) :
    |c - ((indices.map (fun i => a i * a i)).sum +
        (r.sqrt (subtractDot r indices c a a)) ^ 2)| ≤
      gamma (T + 1) u * ((indices.map (fun i => |a i * a i|)).sum +
        |(r.sqrt (subtractDot r indices c a a)) ^ 2|) := by
  have h2T : 2 ≤ T + 1 := by omega
  have hgamma2 : (2 : ℝ) * u < 1 := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast h2T) hu) hgamma
  have hu1 : u < 1 := by linarith
  have hg1 := gamma_nonneg (m := 1) hu (by simpa using hu1)
  have hmono2 := gamma_mono hu h2T hgamma
  cases indices with
  | nil =>
    simp only [subtractDot, List.map_nil, List.sum_nil, zero_add] at hrad ⊢
    exact (rounded_sqrt_residual r c hrad hu hgamma2).trans
      (mul_le_mul_of_nonneg_right hmono2 (abs_nonneg _))
  | cons i indices =>
    let l := i :: indices
    let dot := roundedDot r l a a
    let f := r.sub c dot
    let y := (r.sqrt f) ^ 2
    let S₀ := (l.map (fun i => a i * a i)).sum
    let W := (l.map (fun i => |a i * a i|)).sum
    change |c - (S₀ + y)| ≤ gamma (T + 1) u * (W + |y|)
    have hlen : (l.length : ℝ) * u < 1 := lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by dsimp only [l]; omega : l.length ≤ T + 1)) hu) hgamma
    have hmono := gamma_mono hu (by dsimp only [l]; omega : l.length ≤ T + 1) hgamma
    have h3T : 3 ≤ T + 1 := by simp only [List.length_cons] at hT; omega
    have hmono3 := gamma_mono hu h3T hgamma
    have hgamma3 : ((1 + 2 : ℕ) : ℝ) * u < 1 := lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by exact_mod_cast h3T) hu) hgamma
    have hcoef : gamma 1 u * (1 + gamma 2 u) + gamma 2 u ≤ gamma (T + 1) u := by
      have hg := gamma_add (m := 1) (k := 2) hu hgamma3
      nlinarith
    have hdot : |dot - S₀| ≤ gamma l.length u * W := roundedDot_error r hu l a a hlen
    have hsub : |c - dot - f| ≤ gamma 1 u * |f| :=
      (r.sub_model c dot).abs_error_computed hu hu1
    have hsqrt : |f - y| ≤ gamma 2 u * |y| :=
      rounded_sqrt_residual r f hrad hu hgamma2
    have hf : |f| ≤ (1 + gamma 2 u) * |y| := by
      calc
        |f| = |(f - y) + y| := by congr 1; ring
        _ ≤ |f - y| + |y| := abs_add_le _ _
        _ ≤ gamma 2 u * |y| + |y| := add_le_add hsqrt le_rfl
        _ = _ := by ring
    have hW0 : 0 ≤ W := List.sum_nonneg (fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      exact abs_nonneg _)
    calc
      |c - (S₀ + y)| = |(dot - S₀) + (c - dot - f) + (f - y)| := by congr 1; ring
      _ ≤ |dot - S₀| + |c - dot - f| + |f - y| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ gamma l.length u * W + gamma 1 u * |f| + gamma 2 u * |y| :=
        add_le_add (add_le_add hdot hsub) hsqrt
      _ ≤ gamma l.length u * W + gamma 1 u * ((1 + gamma 2 u) * |y|) +
          gamma 2 u * |y| := by gcongr
      _ = gamma l.length u * W +
          (gamma 1 u * (1 + gamma 2 u) + gamma 2 u) * |y| := by ring
      _ ≤ gamma (T + 1) u * W + gamma (T + 1) u * |y| :=
        add_le_add (mul_le_mul_of_nonneg_right hmono hW0)
          (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _))
      _ = _ := by ring

lemma cholesky_solve_coefficient_le {T : ℕ} {uc : ℝ} (huc : 0 ≤ uc)
    (hgamma : ((T + 1 : ℕ) : ℝ) * uc < 1) :
    gamma (T + 1) uc + 2 * gamma T uc + (gamma T uc) ^ 2 ≤ c₂ T uc := by
  have hm := gamma_mono huc (Nat.le_succ T) hgamma
  unfold c₂
  linarith

lemma beta_nonneg {n T S : ℕ} {us uc : ℝ} (D A Rhat : Mat n) (x b : Vec n)
    (hus : 0 ≤ us) (huc : 0 ≤ uc)
    (hgamma : ((S + n / S - 1 : ℕ) : ℝ) * us < 1)
    (heta : eta T uc D Rhat < 1) : 0 ≤ beta T S us uc D A Rhat x b := by
  have hp : 0 ≤ p D A := matrixInf_nonneg _
  have hc := c₁_nonneg hus hgamma
  have hd := sub_pos.mpr heta
  have hx := vectorInf_nonneg x
  have hb := vectorInf_nonneg b
  have hD := matrixInf_nonneg D⁻¹
  unfold beta
  positivity

lemma G_nonneg {n T : ℕ} {uc : ℝ} (D Rhat : Mat n)
    (huc : 0 ≤ uc) (hgamma : ((T + 1 : ℕ) : ℝ) * uc < 1)
    (i j : Fin n) : 0 ≤ G T uc D Rhat i j := by
  unfold G
  change 0 ≤ c₂ T uc * ((matrixAbs D⁻¹ * matrixAbs Rhat.transpose * matrixAbs Rhat) i j)
  apply mul_nonneg (c₂_nonneg huc hgamma)
  simp only [Matrix.mul_apply, matrixAbs]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg _ (abs_nonneg _)
  exact Finset.sum_nonneg (fun l _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- The componentwise perturbation majorant is exactly the source matrix G. -/
lemma inverse_perturbation_majorant {n T : ℕ} {uc : ℝ}
    (D Rhat Δ : Mat n)
    (hΔ : ∀ i j, |Δ i j| ≤
      c₂ T uc * (matrixAbs Rhat.transpose * matrixAbs Rhat) i j)
    (i j : Fin n) : |(D⁻¹ * Δ) i j| ≤ G T uc D Rhat i j := by
  calc
    |(D⁻¹ * Δ) i j| ≤ ∑ k, |D⁻¹ i k| * |Δ k j| := by
      simpa only [Matrix.mul_apply, abs_mul] using
        Finset.abs_sum_le_sum_abs (fun k => D⁻¹ i k * Δ k j) Finset.univ
    _ ≤ ∑ k, |D⁻¹ i k| *
        (c₂ T uc * (matrixAbs Rhat.transpose * matrixAbs Rhat) k j) :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hΔ k j) (abs_nonneg _))
    _ = G T uc D Rhat i j := by
      unfold G
      rw [Matrix.mul_assoc]
      change (∑ k, |D⁻¹ i k| *
          (c₂ T uc * (matrixAbs Rhat.transpose * matrixAbs Rhat) k j)) =
        c₂ T uc * ∑ k, |D⁻¹ i k| * (matrixAbs Rhat.transpose * matrixAbs Rhat) k j
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The full selected theorem. Success is the interpretation of the source's
"computed Cholesky factors"; all other computational hypotheses are elementary
rounding laws. The two asymptotic conclusions require alpha < 1, whereas the
one-step inequality requires only eta < 1. Empty ambient dimension is allowed.

Statement audit (2026-11-08): /spec/feedback.json reports an unfinished proof,
with no requested statement correction. The statement and constructions are
retained without revision. The size-S sequential tiled reduction is the kernel
specified in paper.tex at the start of the selected proof. Successful Cholesky
completion is made explicit, as in the earlier Cholesky-solve statement; it is
not inferred from SPD. The equivalence ι encodes n = B*T without padding or
changing the ambient coordinates. Arithmetic model laws express the stipulated
absence of overflow/underflow. No bound on q or nonsingularity of A is assumed.

The temporary proof hole belongs only to this theorem. In particular there is
no assumed Cholesky backward error theorem, matrix-vector error certificate,
contraction estimate, or inverse-norm estimate hidden in the input data. -/
theorem mixed_precision_update_form_block_jacobi_in_floating_point_arithmetic
    {n B T S : ℕ} {us uc : ℝ}
    (rs : Arithmetic us) (rc : Arithmetic uc) (cv : Conversion uc)
    (ι : Fin n ≃ Fin B × Fin T)
    (d : Fin B → Mat T) (A N : Mat n) (b x initial : Vec n)
    (hT : 0 < T) (hS : 0 < S) (hdiv : S ∣ n)
    (hus : 0 ≤ us) (hprec : us < uc)
    (hgamma_s : ((S + n / S - 1 : ℕ) : ℝ) * us < 1)
    (hgamma_c : ((T + 1 : ℕ) : ℝ) * uc < 1)
    (hSPD : ∀ l, (d l).PosDef)
    (hsuccess : ∀ l, CholeskySuccessful rc (d l))
    (hdecomp : A = blockDiagonal ι d + N)
    (hsolution : A.mulVec x = b)
    (heta : eta T uc (blockDiagonal ι d) (computedFactor rc ι d) < 1) :
    let D := blockDiagonal ι d
    let Rhat := computedFactor rc ι d
    let v := iterates rs rc cv ι S d A b initial
    let a := alpha T S us uc D N A Rhat
    let z := beta T S us uc D A Rhat x b
    (∀ k : ℕ, vectorInf (error v x (k + 1)) ≤ a * vectorInf (error v x k) + z) ∧
    (a < 1 →
      (∀ k : ℕ, vectorInf (error v x k) ≤
        a ^ k * vectorInf (error v x 0) + (1 - a ^ k) / (1 - a) * z) ∧
      Filter.limsup (fun k : ℕ => vectorInf (error v x k)) Filter.atTop ≤ z / (1 - a)) := by
  let D := blockDiagonal ι d
  let Rhat := computedFactor rc ι d
  let v := iterates rs rc cv ι S d A b initial
  let a := alpha T S us uc D N A Rhat
  let z := beta T S us uc D A Rhat x b
  change (∀ k : ℕ, vectorInf (error v x (k + 1)) ≤ a * vectorInf (error v x k) + z) ∧
    (a < 1 → (∀ k : ℕ, vectorInf (error v x k) ≤
      a ^ k * vectorInf (error v x 0) + (1 - a ^ k) / (1 - a) * z) ∧
      Filter.limsup (fun k : ℕ => vectorInf (error v x k)) Filter.atTop ≤ z / (1 - a))
  have ha : 0 ≤ a := alpha_nonneg D N A Rhat hus (hus.trans hprec.le) hgamma_s heta
  have hstep : ∀ k : ℕ,
      vectorInf (error v x (k + 1)) ≤ a * vectorInf (error v x k) + z := by
    sorry
  refine ⟨hstep, fun hlt => ⟨?_, ?_⟩⟩
  · exact affine_recurrence_bound (fun k => vectorInf (error v x k)) ha hlt hstep
  · exact affine_recurrence_limsup (fun k => vectorInf (error v x k)) ha hlt
      (fun _ => vectorInf_nonneg _) hstep

end MixedPrecisionBlockJacobi
