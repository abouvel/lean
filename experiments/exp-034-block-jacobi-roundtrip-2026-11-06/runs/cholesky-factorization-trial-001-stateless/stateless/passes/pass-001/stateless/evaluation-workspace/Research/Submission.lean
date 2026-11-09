import Mathlib

/-!
# Cholesky factorization: statement and primitive execution model

The target is `Cholesky.cholesky_factorization`, corresponding to the full
active theorem `theorem:cholesky_factorization` in `/spec/source.txt`.
Only its proof is left for the next role. No scalar backward-error result is
assumed by the execution model.

Indices are zero based: Lean pivot `i` is paper pivot `i + 1`.
The sequential dot product initializes from its first rounded product; an
empty dot product is zero. At pivot zero the algorithm directly uses the
input entry (subtracting the empty sum is exact for a floating-point input).

The source's four-operation display alone does not specify square root.
Here standard rounded square root means rounding the exact real square root
with the SAME rounding map as the other operations. Its error guarantee is
therefore an instance of `FloatingPoint.relative_round`, not a diagonal
backward-error assumption. This modeling interpretation is explicit in the
statement through `fp : FloatingPoint u`.
-/

namespace Cholesky

noncomputable section

/-- A rounding map on real exact results. `InRange x` says the exact result
`x` is within the regime without overflow or underflow, including zero.
The standard relative rounding guarantee is supplied uniformly for all such
results; it applies to exact square roots as well as arithmetic results. -/
structure FloatingPoint (u : ℝ) where
  round : ℝ → ℝ
  InRange : ℝ → Prop
  relative_round : ∀ x, InRange x → ∃ δ : ℝ, |δ| ≤ u ∧ round x = x * (1 + δ)

/-- The paper's deterministic rounding-error constant. -/
def gamma (m : ℕ) (u : ℝ) : ℝ :=
  (m : ℝ) * u / (1 - (m : ℝ) * u)

/-- Entrywise absolute value, not a matrix norm. -/
def entryAbs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => |A i j|

/-- The concrete symmetric backward-error candidate. -/
def perturbation {n : ℕ} (A R : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  R.transpose * R - A

/-- Remaining steps of a left-to-right rounded dot product. -/
def dotTail {u : ℝ} (fp : FloatingPoint u) (s : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => s
  | p :: ps => dotTail fp (fp.round (s + fp.round (p.1 * p.2))) ps

/-- Sequential dot product: no artificial addition to zero for the first term. -/
def roundedDot {u : ℝ} (fp : FloatingPoint u) : List (ℝ × ℝ) → ℝ
  | [] => 0
  | p :: ps => dotTail fp (fp.round (p.1 * p.2)) ps

/-- Every multiplication and addition in the tail has an in-range exact result. -/
def dotTailInRange {u : ℝ} (fp : FloatingPoint u) (s : ℝ) : List (ℝ × ℝ) → Prop
  | [] => True
  | p :: ps =>
      fp.InRange (p.1 * p.2) ∧
      fp.InRange (s + fp.round (p.1 * p.2)) ∧
      dotTailInRange fp (fp.round (s + fp.round (p.1 * p.2))) ps

/-- Absence of overflow and underflow for a sequential dot product. -/
def dotInRange {u : ℝ} (fp : FloatingPoint u) : List (ℝ × ℝ) → Prop
  | [] => True
  | p :: ps => fp.InRange (p.1 * p.2) ∧
      dotTailInRange fp (fp.round (p.1 * p.2)) ps

/-- Products with indices `k < i`, in increasing order. At `i = j` these
are the squares in the diagonal update. -/
def prefixPairs {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    List (ℝ × ℝ) :=
  List.ofFn (fun k : Fin i.val =>
    (R ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ i,
     R ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ j))

/-- Rounded numerator of the update. An empty prefix needs no subtraction. -/
def updateNumerator {n : ℕ} {u : ℝ} (fp : FloatingPoint u)
    (A R : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  if i.val = 0 then A i j
  else fp.round (A i j - roundedDot fp (prefixPairs R i j))

/-- Primitive successful execution of the upper-triangular Cholesky algorithm.
All right sides depend only on earlier columns/rows and the current pivot.
Nonnegative radicands permit real square root; every division has a nonzero
pivot. A zero last pivot is permitted if no division uses it. -/
structure SuccessfulRun {n : ℕ} {u : ℝ} (fp : FloatingPoint u)
    (A R : Matrix (Fin n) (Fin n) ℝ) : Prop where
  upper_triangular : ∀ i j, j < i → R i j = 0
  radicand_nonneg : ∀ j, 0 ≤ updateNumerator fp A R j j
  diagonal : ∀ j, R j j = fp.round (Real.sqrt (updateNumerator fp A R j j))
  pivot_ne_zero : ∀ i j, i < j → R i i ≠ 0
  off_diagonal : ∀ i j, i < j →
    R i j = fp.round (updateNumerator fp A R i j / R i i)

/-- The no-overflow/no-underflow assumption, for exactly the operations used
by the execution above. No error estimate on a matrix residual appears here. -/
structure NoOverflowUnderflow {n : ℕ} {u : ℝ} (fp : FloatingPoint u)
    (A R : Matrix (Fin n) (Fin n) ℝ) : Prop where
  dots : ∀ i j, i ≤ j → dotInRange fp (prefixPairs R i j)
  subtractions : ∀ i j, i ≤ j → i.val ≠ 0 →
    fp.InRange (A i j - roundedDot fp (prefixPairs R i j))
  divisions : ∀ i j, i < j →
    fp.InRange (updateNumerator fp A R i j / R i i)
  square_roots : ∀ j, fp.InRange (Real.sqrt (updateNumerator fp A R j j))

/-- Scalar rounding-product certificate. -/
def Good (u : ℝ) (m : ℕ) (x : ℝ) : Prop :=
  0 ≤ x ∧ 1 - m * u ≤ x ∧ x * (1 - m * u) ≤ 1

lemma small_of_le {u : ℝ} {a b : ℕ} (hu : 0 ≤ u)
    (hb : (b : ℝ) * u < 1) (hab : a ≤ b) : (a : ℝ) * u < 1 :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hu) hb

lemma good_one (u : ℝ) : Good u 0 1 := by simp [Good]

lemma good_mono {u x : ℝ} {a b : ℕ} (hu : 0 ≤ u) (hab : a ≤ b)
    (h : Good u a x) : Good u b x := by
  have hmul : (a : ℝ) * u ≤ b * u :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hu
  rcases h with ⟨hx, hl, hr⟩
  exact ⟨hx, by linarith, by nlinarith⟩

lemma good_mul {u x y : ℝ} {a b : ℕ} (hu : 0 ≤ u)
    (hs : ((a + b : ℕ) : ℝ) * u < 1)
    (hx : Good u a x) (hy : Good u b y) : Good u (a+b) (x*y) := by
  have ha := small_of_le hu hs (Nat.le_add_right a b)
  have hb := small_of_le hu hs (Nat.le_add_left b a)
  rcases hx with ⟨hx, hxl, hxr⟩
  rcases hy with ⟨hy, hyl, hyr⟩
  have hau : 0 ≤ (a : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hbu : 0 ≤ (b : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hl := mul_le_mul hxl hyl (by linarith : 0 ≤ 1 - (b : ℝ)*u) hx
  have hr := mul_le_mul hxr hyr (mul_nonneg hy (by linarith)) (by norm_num : (0:ℝ) ≤ 1)
  have hprod : 0 ≤ (a : ℝ)*u*((b : ℝ)*u) := mul_nonneg hau hbu
  simp only [Nat.cast_add] at hs ⊢
  refine ⟨mul_nonneg hx hy, ?_, ?_⟩
  <;> simp only [Nat.cast_add]
  · nlinarith
  · have : 0 ≤ x*y*((a:ℝ)*u*((b:ℝ)*u)) := mul_nonneg (mul_nonneg hx hy) hprod
    nlinarith

lemma good_round {u d : ℝ} (hu : 0 ≤ u) (hs : u < 1) (hd : |d| ≤ u) :
    Good u 1 (1+d) ∧ Good u 1 (1+d)⁻¹ := by
  have hd' := abs_le.mp hd
  have hp : 0 < 1+d := by linarith
  constructor
  · simp only [Good, Nat.cast_one, one_mul]
    refine ⟨le_of_lt hp, by linarith, ?_⟩
    have : 0 ≤ u*(u-d) := mul_nonneg hu (by linarith)
    nlinarith
  · simp only [Good, Nat.cast_one, one_mul]
    refine ⟨le_of_lt (inv_pos.mpr hp), ?_, ?_⟩
    · rw [inv_eq_one_div]
      apply (le_div_iff₀ hp).2
      have : 0 ≤ u*(u-d) := mul_nonneg hu (by linarith)
      nlinarith
    · apply (inv_mul_le_iff₀ hp).2
      linarith

lemma good_error {u x : ℝ} {m : ℕ} (hu : 0 ≤ u)
    (hs : (m : ℝ)*u < 1) (hx : Good u m x) : |x-1| ≤ gamma m u := by
  rcases hx with ⟨hx, hl, hr⟩
  have hp : 0 < 1-(m:ℝ)*u := by linarith
  have hm : 0 ≤ (m:ℝ)*u := mul_nonneg (Nat.cast_nonneg _) hu
  rw [abs_le]
  constructor
  · rw [neg_le_sub_iff_le_add, gamma]
    have : (m:ℝ)*u ≤ (m:ℝ)*u / (1-(m:ℝ)*u) := by
      apply (le_div_iff₀ hp).2
      nlinarith [sq_nonneg ((m:ℝ)*u)]
    linarith
  · rw [gamma, le_div_iff₀ hp]
    nlinarith

lemma gamma_nonneg {u : ℝ} {m : ℕ} (hu : 0 ≤ u) (hs : (m:ℝ)*u < 1) :
    0 ≤ gamma m u := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

lemma gamma_mono {u : ℝ} {a b : ℕ} (hu : 0 ≤ u)
    (hs : (b:ℝ)*u < 1) (hab : a ≤ b) : gamma a u ≤ gamma b u := by
  have ha := small_of_le hu hs hab
  have hh : (a:ℝ)*u ≤ (b:ℝ)*u := mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hu
  rw [gamma, gamma, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma gamma_comp {u : ℝ} {a b : ℕ} (hu : 0 ≤ u)
    (hs : ((a+b:ℕ):ℝ)*u < 1) :
    gamma a u + gamma b u + gamma a u * gamma b u ≤ gamma (a+b) u := by
  have ha := small_of_le hu hs (Nat.le_add_right a b)
  have hb := small_of_le hu hs (Nat.le_add_left b a)
  have hga := gamma_nonneg hu ha
  have hgb := gamma_nonneg hu hb
  have hgooda : Good u a (1 + gamma a u) := by
    unfold Good gamma
    have hp : 0 < 1-(a:ℝ)*u := by linarith
    refine ⟨by positivity, ?_, ?_⟩
    · have : 0 ≤ (a:ℝ)*u := mul_nonneg (Nat.cast_nonneg _) hu
      have hg : 0 ≤ (a:ℝ)*u / (1-(a:ℝ)*u) := by positivity
      linarith
    · field_simp
      <;> nlinarith
  have hgoodb : Good u b (1 + gamma b u) := by
    unfold Good gamma
    have hp : 0 < 1-(b:ℝ)*u := by linarith
    refine ⟨by positivity, ?_, ?_⟩
    · have : 0 ≤ (b:ℝ)*u := mul_nonneg (Nat.cast_nonneg _) hu
      have hg : 0 ≤ (b:ℝ)*u / (1-(b:ℝ)*u) := by positivity
      linarith
    · field_simp
      <;> nlinarith
  have h := good_error hu hs (good_mul hu hs hgooda hgoodb)
  have hh := le_trans (le_abs_self ((1+gamma a u)*(1+gamma b u)-1)) h
  nlinarith

lemma round_error {u : ℝ} (fp : FloatingPoint u) {x : ℝ}
    (hx : fp.InRange x) : |fp.round x - x| ≤ u * |x| := by
  obtain ⟨d, hd, he⟩ := fp.relative_round x hx
  rw [he]
  calc
    |x*(1+d)-x| = |d| * |x| := by rw [show x*(1+d)-x = d*x by ring, abs_mul]
    _ ≤ u*|x| := mul_le_mul_of_nonneg_right hd (abs_nonneg _)

lemma round_error_gamma {u : ℝ} (fp : FloatingPoint u) (hu : 0 ≤ u)
    (hs : u < 1) {x : ℝ} (hx : fp.InRange x) :
    |fp.round x-x| ≤ gamma 1 u * |x| := by
  have h : u ≤ gamma 1 u := by
    simp only [gamma, Nat.cast_one, one_mul]
    apply (le_div_iff₀ (by linarith : 0 < 1-u)).2
    nlinarith [sq_nonneg u]
  exact (round_error fp hx).trans (mul_le_mul_of_nonneg_right h (abs_nonneg _))

def exactDot (ps : List (ℝ × ℝ)) : ℝ := (ps.map (fun p => p.1*p.2)).sum
def absDot (ps : List (ℝ × ℝ)) : ℝ := (ps.map (fun p => |p.1*p.2|)).sum

lemma absDot_nonneg (ps : List (ℝ × ℝ)) : 0 ≤ absDot ps := by
  unfold absDot
  induction ps with
  | nil => simp
  | cons p ps ih => simpa using add_nonneg (abs_nonneg (p.1*p.2)) ih

lemma exactDot_abs (ps : List (ℝ × ℝ)) : |exactDot ps| ≤ absDot ps := by
  induction ps with
  | nil => simp [exactDot, absDot]
  | cons p ps ih =>
    simpa [exactDot, absDot] using (abs_add_le (p.1*p.2) (exactDot ps)).trans
      (add_le_add (le_refl |p.1*p.2|) ih)

lemma dot_step {u : ℝ} (fp : FloatingPoint u) (hu : 0 ≤ u)
    {m : ℕ} (hm : 1 ≤ m) (hs : ((m+1:ℕ):ℝ)*u < 1)
    {s S W t : ℝ} (hS : |S| ≤ W) (he : |s-S| ≤ gamma m u * W)
    (ht : fp.InRange t) (ha : fp.InRange (s+fp.round t)) :
    |fp.round (s+fp.round t) - (S+t)| ≤ gamma (m+1) u * (W+|t|) := by
  have hs1 : u < 1 := by simpa using small_of_le hu hs (show 1 ≤ m+1 by omega)
  have gm := gamma_nonneg hu (small_of_le hu hs (Nat.le_succ m))
  have g1 := gamma_nonneg (m := 1) hu (by simpa using hs1)
  have hv := round_error_gamma fp hu hs1 ht
  have hr := round_error_gamma fp hu hs1 ha
  have hsa : |s| ≤ (1+gamma m u)*W := by
    have hh := abs_add_le (s-S) S
    rw [sub_add_cancel] at hh
    nlinarith
  have hva : |fp.round t| ≤ (1+gamma 1 u)*|t| := by
    have hh := abs_add_le (fp.round t-t) t
    rw [sub_add_cancel] at hh
    nlinarith
  have hsum := abs_add_le s (fp.round t)
  have htriangle : |fp.round (s+fp.round t)-(S+t)| ≤
      |fp.round (s+fp.round t)-(s+fp.round t)| + |s-S| + |fp.round t-t| := by
    have h := abs_add_le (fp.round (s+fp.round t)-(s+fp.round t)) ((s-S)+(fp.round t-t))
    have h' := abs_add_le (s-S) (fp.round t-t)
    have hid : fp.round (s+fp.round t)-(s+fp.round t)+((s-S)+(fp.round t-t)) =
        fp.round (s+fp.round t)-(S+t) := by ring
    rw [hid] at h
    linarith
  have hc := gamma_comp hu hs
  have hs2 : ((1+1:ℕ):ℝ)*u < 1 := small_of_le hu hs (by omega)
  have hc2 := gamma_comp hu hs2 (a := 1) (b := 1)
  have hmono := gamma_mono hu hs (show 1+1 ≤ m+1 by omega)
  have hW : 0 ≤ W := (abs_nonneg S).trans hS
  have hb1 := mul_le_mul_of_nonneg_right hc hW
  have hb2 := mul_le_mul_of_nonneg_right (hc2.trans hmono) (abs_nonneg t)
  have hb3 := mul_le_mul_of_nonneg_left (hsa) g1
  have hb4 := mul_le_mul_of_nonneg_left (hva) g1
  have hb5 := mul_le_mul_of_nonneg_left hsum g1
  nlinarith

lemma dotTail_error {u : ℝ} (fp : FloatingPoint u) (hu : 0 ≤ u)
    (ps : List (ℝ × ℝ)) : ∀ (m : ℕ) (s S W : ℝ), 1 ≤ m →
    ((m+ps.length:ℕ):ℝ)*u < 1 → |S| ≤ W →
    |s-S| ≤ gamma m u * W → dotTailInRange fp s ps →
    |dotTail fp s ps - (S+exactDot ps)| ≤
      gamma (m+ps.length) u * (W+absDot ps) := by
  induction ps with
  | nil => intro m s S W hm hs hS he hr; simpa [dotTail, exactDot, absDot] using he
  | cons p ps ih =>
    intro m s S W hm hs hS he hr
    rcases hr with ⟨ht, ha, hr⟩
    have hstep := dot_step fp hu hm (small_of_le hu hs (by simp)) hS he ht ha
    have hS' : |S+p.1*p.2| ≤ W+|p.1*p.2| :=
      (abs_add_le _ _).trans (add_le_add hS (le_refl _))
    have h := ih (m+1) _ (S+p.1*p.2) (W+|p.1*p.2|) (by omega)
      (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs)
      hS' hstep hr
    simpa [dotTail, exactDot, absDot, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      add_assoc] using h

lemma roundedDot_error {u : ℝ} (fp : FloatingPoint u) (hu : 0 ≤ u)
    (ps : List (ℝ × ℝ)) (hs : (ps.length:ℝ)*u < 1) (hr : dotInRange fp ps) :
    |roundedDot fp ps - exactDot ps| ≤ gamma ps.length u * absDot ps := by
  cases ps with
  | nil => simp [roundedDot, exactDot, absDot, gamma]
  | cons p ps =>
    rcases hr with ⟨ht, hr⟩
    have hs1 : u < 1 := by simpa using small_of_le hu hs (show 1 ≤ (p::ps).length by simp)
    have he := round_error_gamma fp hu hs1 ht
    have h := dotTail_error fp hu ps 1 (fp.round (p.1*p.2)) (p.1*p.2) |p.1*p.2|
      (by omega) (by simpa [List.length_cons, Nat.add_comm] using hs) (le_refl _) he hr
    simpa [roundedDot, exactDot, absDot, Nat.add_comm] using h

lemma prefixPairs_length {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (prefixPairs R i j).length = i.val := by simp [prefixPairs]

lemma update_recover {n : ℕ} {u : ℝ} (fp : FloatingPoint u)
    (A R : Matrix (Fin n) (Fin n) ℝ) (hu : 0 ≤ u) (hs : u < 1)
    (hr : NoOverflowUnderflow fp A R) (i j : Fin n) (hij : i ≤ j) :
    ∃ c, Good u (if i.val = 0 then 0 else 1) c ∧
      A i j = roundedDot fp (prefixPairs R i j) + updateNumerator fp A R i j*c := by
  by_cases hi : i.val = 0
  · have hp : prefixPairs R i j = [] := by
      apply List.eq_nil_iff_length_eq_zero.mpr
      simpa [prefixPairs_length] using hi
    exact ⟨1, by simpa [hi] using good_one u, by simp [updateNumerator, hi, hp, roundedDot]⟩
  · obtain ⟨d, hd, he⟩ := fp.relative_round _ (hr.subtractions i j hij hi)
    have hn : 1+d ≠ 0 := by have := abs_le.mp hd; linarith
    refine ⟨(1+d)⁻¹, by simpa [hi] using (good_round hu hs hd).2, ?_⟩
    simp only [updateNumerator, hi, ↓reduceIte, he]
    field_simp
    <;> ring

lemma pivot_recover {n : ℕ} {u : ℝ} (fp : FloatingPoint u)
    (A R : Matrix (Fin n) (Fin n) ℝ) (hu : 0 ≤ u)
    (hs : ((n+1:ℕ):ℝ)*u < 1) (hrun : SuccessfulRun fp A R)
    (hr : NoOverflowUnderflow fp A R) (i j : Fin n) (hij : i ≤ j) :
    ∃ c, Good u (n+1) c ∧
      A i j = roundedDot fp (prefixPairs R i j) + (R i i*R i j)*c := by
  have hs1 : u < 1 := by simpa using small_of_le hu hs (show 1 ≤ n+1 by omega)
  obtain ⟨cs, hcs, he⟩ := update_recover fp A R hu hs1 hr i j hij
  let m : ℕ := if i.val = 0 then 0 else 1
  have hm : m ≤ 1 := by dsimp [m]; split <;> omega
  have hcs' : Good u m cs := hcs
  by_cases heq : i = j
  · subst j
    obtain ⟨d, hd, hdEq⟩ := fp.relative_round _ (hr.square_roots i)
    have hn : 1+d ≠ 0 := by have := abs_le.mp hd; linarith
    have hcount : m+2 ≤ n+1 := by
      dsimp [m]; split <;> have := i.isLt <;> omega
    have hs2 := small_of_le hu hs (show 1+1 ≤ n+1 by have := i.isLt; omega)
    have hc2 := good_mul hu hs2 (good_round hu hs1 hd).2 (good_round hu hs1 hd).2
    have hcm := good_mul hu (small_of_le hu hs hcount) hcs' hc2
    refine ⟨cs*((1+d)⁻¹*(1+d)⁻¹), good_mono hu hcount hcm, ?_⟩
    have hdiag := hrun.diagonal i
    rw [hdEq] at hdiag
    have hsq := Real.sq_sqrt (hrun.radicand_nonneg i)
    have hnum : updateNumerator fp A R i i = (R i i*R i i)*((1+d)⁻¹*(1+d)⁻¹) := by
      rw [hdiag]
      field_simp
      nlinarith [hsq]
    rw [hnum] at he
    nlinarith [he]
  · have hlt : i < j := lt_of_le_of_ne hij heq
    obtain ⟨d, hd, hdEq⟩ := fp.relative_round _ (hr.divisions i j hlt)
    have hn : 1+d ≠ 0 := by have := abs_le.mp hd; linarith
    have hcount : m+1 ≤ n+1 := by have := i.isLt; omega
    have hcm := good_mul hu (small_of_le hu hs hcount) hcs' (good_round hu hs1 hd).2
    refine ⟨cs*(1+d)⁻¹, good_mono hu hcount hcm, ?_⟩
    have hoff := hrun.off_diagonal i j hlt
    rw [hdEq] at hoff
    have hp := hrun.pivot_ne_zero i j hlt
    have hnum : updateNumerator fp A R i j = (R i i*R i j)*(1+d)⁻¹ := by
      rw [hoff]
      field_simp
      <;> ring
    rw [hnum] at he
    nlinarith [he]

lemma local_error {n : ℕ} {u : ℝ} (fp : FloatingPoint u)
    (A R : Matrix (Fin n) (Fin n) ℝ) (hu : 0 ≤ u)
    (hs : ((n+1:ℕ):ℝ)*u < 1) (hrun : SuccessfulRun fp A R)
    (hr : NoOverflowUnderflow fp A R) (i j : Fin n) (hij : i ≤ j) :
    |exactDot (prefixPairs R i j) + R i i*R i j - A i j| ≤
      gamma (n+1) u * (absDot (prefixPairs R i j) + |R i i*R i j|) := by
  obtain ⟨c, hc, he⟩ := pivot_recover fp A R hu hs hrun hr i j hij
  have hce := good_error hu hs hc
  have hd := roundedDot_error fp hu (prefixPairs R i j)
    (by rw [prefixPairs_length]; exact small_of_le hu hs (by have := i.isLt; omega))
    (hr.dots i j hij)
  have hm := gamma_mono hu hs (show (prefixPairs R i j).length ≤ n+1 by
    rw [prefixPairs_length]; have := i.isLt; omega)
  have hde := hd.trans (mul_le_mul_of_nonneg_right hm (absDot_nonneg _))
  calc
    |exactDot (prefixPairs R i j) + R i i*R i j - A i j| =
        |(exactDot (prefixPairs R i j)-roundedDot fp (prefixPairs R i j)) +
          (R i i*R i j)*(1-c)| := by rw [he]; congr 1; ring
    _ ≤ |exactDot (prefixPairs R i j)-roundedDot fp (prefixPairs R i j)| +
        |R i i*R i j| * |1-c| := by simpa [abs_mul] using (abs_add_le
          (exactDot (prefixPairs R i j)-roundedDot fp (prefixPairs R i j)) ((R i i*R i j)*(1-c)))
    _ ≤ gamma (n+1) u * absDot (prefixPairs R i j) +
        |R i i*R i j| * gamma (n+1) u := by
      rw [abs_sub_comm (exactDot _) (roundedDot _ _), abs_sub_comm 1 c]
      exact add_le_add hde (mul_le_mul_of_nonneg_left hce (abs_nonneg _))
    _ = _ := by ring

lemma prefix_sum {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hf : ∀ k, i < k → f k = 0) :
    ∑ k, f k = (∑ k : Fin i.val, f ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩) + f i := by
  classical
  have hs : (∑ k ∈ Finset.Iic i, f k) = ∑ k, f k :=
    Finset.sum_subset (Finset.subset_univ _) (by
      intro k hk hn
      exact hf k (lt_of_not_ge (by simpa using hn)))
  rw [← hs, ← Finset.Iio_insert, Finset.sum_insert (by simp), add_comm]
  congr 1
  symm
  apply Finset.sum_bij (fun (k : Fin i.val) _ => (⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ : Fin n))
  · intro k hk; exact Finset.mem_Iio.mpr k.isLt
  · intro a ha b hb hab; exact Fin.ext (congrArg (fun z : Fin n => z.val) hab)
  · intro k hk
    refine ⟨⟨k.val, by simpa using hk⟩, Finset.mem_univ _, ?_⟩
    rfl
  · intro k hk; rfl

lemma gram_prefix {n : ℕ} {u : ℝ} (fp : FloatingPoint u)
    (A R : Matrix (Fin n) (Fin n) ℝ) (hr : SuccessfulRun fp A R) (i j : Fin n) :
    (R.transpose*R) i j = exactDot (prefixPairs R i j) + R i i*R i j := by
  rw [Matrix.mul_apply]
  have h := prefix_sum i (fun k => R k i*R k j) (by
    intro k hk; dsimp only; rw [hr.upper_triangular k i hk, zero_mul])
  simpa [exactDot, prefixPairs, List.map_ofFn, List.sum_ofFn] using h

lemma abs_gram_prefix {n : ℕ} {u : ℝ} (fp : FloatingPoint u)
    (A R : Matrix (Fin n) (Fin n) ℝ) (hr : SuccessfulRun fp A R) (i j : Fin n) :
    (entryAbs R.transpose*entryAbs R) i j = absDot (prefixPairs R i j) + |R i i*R i j| := by
  rw [Matrix.mul_apply]
  have h := prefix_sum i (fun k => |R k i*R k j|) (by
    intro k hk; dsimp only; rw [hr.upper_triangular k i hk, zero_mul, abs_zero])
  simpa [entryAbs, absDot, prefixPairs, List.map_ofFn, List.sum_ofFn, abs_mul] using h


/-- **Cholesky Factorization** (the complete selected source statement).
For every dimension, including zero, every symmetric positive definite input,
and every successful primitive rounded Cholesky run without overflow or
underflow, the computed upper factor has a symmetric componentwise backward
error bounded by exactly `gamma (n + 1) u` times its absolute Gram product.
`hu` makes explicit the nonnegativity inherent in a unit roundoff.
Symmetry is written explicitly in addition to real positive definiteness. -/
theorem cholesky_factorization
    {n : ℕ} (A R : Matrix (Fin n) (Fin n) ℝ)
    (u : ℝ) (fp : FloatingPoint u)
    (hA_symm : A.IsSymm) (hA_pos : A.PosDef)
    (hu : 0 ≤ u) (hsmall : ((n + 1 : ℕ) : ℝ) * u < 1)
    (hrun : SuccessfulRun fp A R)
    (hrange : NoOverflowUnderflow fp A R) :
    ∃ ΔA : Matrix (Fin n) (Fin n) ℝ,
      ΔA.IsSymm ∧
      R.transpose * R = A + ΔA ∧
      ∀ i j, |ΔA i j| ≤ gamma (n + 1) u *
        (entryAbs R.transpose * entryAbs R) i j := by
  classical
  have hg : (R.transpose * R).IsSymm := by
    unfold Matrix.IsSymm
    simp [Matrix.transpose_mul]
  have habs : (entryAbs R.transpose * entryAbs R).IsSymm := by
    unfold Matrix.IsSymm
    have ht : entryAbs R.transpose = (entryAbs R).transpose := rfl
    rw [ht]
    simp [Matrix.transpose_mul]
  refine ⟨perturbation A R, ?_, ?_, ?_⟩
  · unfold perturbation Matrix.IsSymm
    rw [Matrix.transpose_sub, hg, hA_symm]
  · unfold perturbation
    abel
  · intro i j
    have upper : ∀ i j, i ≤ j → |perturbation A R i j| ≤
        gamma (n+1) u * (entryAbs R.transpose * entryAbs R) i j := by
      intro i j hij
      have h := local_error fp A R hu hsmall hrun hrange i j hij
      rw [← gram_prefix fp A R hrun i j, ← abs_gram_prefix fp A R hrun i j] at h
      exact h
    by_cases hij : i ≤ j
    · exact upper i j hij
    · have h := upper j i (le_of_not_ge hij)
      have hd : perturbation A R j i = perturbation A R i j := by
        simp only [perturbation, Matrix.sub_apply, hg.apply i j, hA_symm.apply i j]
      rw [hd, habs.apply i j] at h
      exact h

end

end Cholesky
