import Research.Common.FloatingPoint.Model

/-!
# Rounded Horner evaluation

Coefficients are listed in increasing degree order. The error envelope uses
only exact evaluation and the relative-error parameter; it is independent of
the rounding operation. The final proof is left to the proof role.
-/

namespace Research.Horner

/-- Exact Horner evaluation, with coefficients in increasing degree order. -/
def P : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: tail, x => a + x * P tail x

/-- Horner evaluation with one rounded multiplication and one rounded addition
at each list step. -/
def Q (model : Research.FloatingPoint.Model) : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: tail, x => model.round (a + model.round (x * Q model tail x))

/-- The prescribed forward-error envelope, computed entirely from exact data. -/
def E : List ℝ → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | a :: tail, x, u =>
      let v := P tail x
      let e := E tail x u
      u * |a + x * v| + (1 + u) * (u * |x * v| + (1 + u) * |x| * e)

@[simp] theorem P_nil (x : ℝ) : P [] x = 0 := rfl

@[simp] theorem P_cons (a : ℝ) (tail : List ℝ) (x : ℝ) :
    P (a :: tail) x = a + x * P tail x := rfl

@[simp] theorem Q_nil (model : Research.FloatingPoint.Model) (x : ℝ) :
    Q model [] x = 0 := rfl

@[simp] theorem Q_cons (model : Research.FloatingPoint.Model)
    (a : ℝ) (tail : List ℝ) (x : ℝ) :
    Q model (a :: tail) x = model.round (a + model.round (x * Q model tail x)) := rfl

@[simp] theorem E_nil (x u : ℝ) : E [] x u = 0 := rfl

@[simp] theorem E_cons (a : ℝ) (tail : List ℝ) (x u : ℝ) :
    E (a :: tail) x u =
      u * |a + x * P tail x| +
        (1 + u) * (u * |x * P tail x| + (1 + u) * |x| * E tail x u) := rfl

/-- Absolute error of a single rounding. -/
lemma round_error (model : Research.FloatingPoint.Model) (z : ℝ) :
    |model.round z - z| ≤ model.u * |z| := by
  obtain ⟨δ, hδ, hr⟩ := model.round_spec z
  rw [hr]
  calc
    |z * (1 + δ) - z| = |z| * |δ| := by
      rw [show z * (1 + δ) - z = z * δ by ring, abs_mul]
    _ ≤ |z| * model.u := mul_le_mul_of_nonneg_left hδ (abs_nonneg z)
    _ = model.u * |z| := mul_comm _ _

/-- Error relative to an arbitrary reference value. -/
lemma round_perturbation (model : Research.FloatingPoint.Model) (z t : ℝ) :
    |model.round z - t| ≤ model.u * |t| + (1 + model.u) * |z - t| := by
  have hz : |z| ≤ |t| + |z - t| := by
    calc
      |z| = |t + (z - t)| := by congr 1; ring
      _ ≤ |t| + |z - t| := abs_add_le _ _
  calc
    |model.round z - t| = |(model.round z - z) + (z - t)| := by
      congr 1; ring
    _ ≤ |model.round z - z| + |z - t| := abs_add_le _ _
    _ ≤ model.u * |z| + |z - t| := add_le_add (round_error model z) (le_refl _)
    _ ≤ model.u * (|t| + |z - t|) + |z - t| :=
      add_le_add (mul_le_mul_of_nonneg_left hz model.u_nonneg) (le_refl _)
    _ = model.u * |t| + (1 + model.u) * |z - t| := by ring

/-- Universal forward-error bound in the supplied relative-error model.
The only rounding assumptions are the fields of `model`: nonnegativity of
`model.u` and its existential relative-error law. No restrictions are imposed
on the coefficient list, the real input, or the size of `model.u`.
-/
theorem forward_error_bound (model : Research.FloatingPoint.Model)
    (coefficients : List ℝ) (x : ℝ) :
    |Q model coefficients x - P coefficients x| ≤ E coefficients x model.u := by
  have hu : 0 ≤ 1 + model.u := by linarith [model.u_nonneg]
  induction coefficients with
  | nil => simp
  | cons a tail ih =>
    have hm : |model.round (x * Q model tail x) - x * P tail x| ≤
        model.u * |x * P tail x| +
          (1 + model.u) * |x| * E tail x model.u := by
      calc
        _ ≤ model.u * |x * P tail x| +
            (1 + model.u) * |x * Q model tail x - x * P tail x| :=
          round_perturbation model _ _
        _ = model.u * |x * P tail x| +
            (1 + model.u) * |x| * |Q model tail x - P tail x| := by
          rw [← mul_sub x (Q model tail x) (P tail x), abs_mul x (Q model tail x - P tail x)]
          ring
        _ ≤ _ := add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left ih (mul_nonneg hu (abs_nonneg x)))
    simp only [Q_cons, P_cons, E_cons]
    calc
      _ ≤ model.u * |a + x * P tail x| +
          (1 + model.u) * |(a + model.round (x * Q model tail x)) -
            (a + x * P tail x)| := round_perturbation model _ _
      _ = model.u * |a + x * P tail x| +
          (1 + model.u) * |model.round (x * Q model tail x) - x * P tail x| := by
        rw [add_sub_add_left_eq_sub]
      _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hm hu)

end Research.Horner
