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

/-- The full selected theorem. Success is the interpretation of the source's
"computed Cholesky factors"; all other computational hypotheses are elementary
rounding laws. The two asymptotic conclusions require alpha < 1, whereas the
one-step inequality requires only eta < 1. Empty ambient dimension is allowed.

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
