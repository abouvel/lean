import Research.Common.FloatingPoint.Model

/-!
# Rounded Horner evaluation with the prescribed forward-error envelope

Coefficients are listed in increasing degree order. The model assumptions are
exactly those in `Research.FloatingPoint.Model`: nonnegative unit roundoff and
the relative-error law for every real argument.

Statement revision record: no `/spec/feedback.json` was present. This initial
statement follows `/spec/source.txt` without additional assumptions or changes
to the prescribed recurrences.
-/

namespace Research.FloatingPoint.Horner

/-- Exact Horner evaluation for coefficients in increasing degree order. -/
def P : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: tail, x => a + x * P tail x

/-- Rounded Horner evaluation: one rounded product and one rounded sum at
 every list step, including the last nonempty step. -/
def Q (model : Model) : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: tail, x => model.round (a + model.round (x * Q model tail x))

/-- The prescribed envelope, computed solely from exact evaluation, the
coefficients, the argument, and the real parameter `u`. -/
def E : List ℝ → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | a :: tail, x, u =>
      let v := P tail x
      let e := E tail x u
      u * |a + x * v| + (1 + u) * (u * |x * v| + (1 + u) * |x| * e)

@[simp] theorem P_nil (x : ℝ) : P [] x = 0 := rfl

@[simp] theorem P_cons (a : ℝ) (tail : List ℝ) (x : ℝ) :
    P (a :: tail) x = a + x * P tail x := rfl

@[simp] theorem Q_nil (model : Model) (x : ℝ) : Q model [] x = 0 := rfl

@[simp] theorem Q_cons (model : Model) (a : ℝ) (tail : List ℝ) (x : ℝ) :
    Q model (a :: tail) x = model.round (a + model.round (x * Q model tail x)) := rfl

@[simp] theorem E_nil (x u : ℝ) : E [] x u = 0 := rfl

@[simp] theorem E_cons (a : ℝ) (tail : List ℝ) (x u : ℝ) :
    E (a :: tail) x u =
      u * |a + x * P tail x| +
        (1 + u) * (u * |x * P tail x| + (1 + u) * |x| * E tail x u) := rfl

theorem round_error (model : Model) (z : ℝ) :
    |model.round z - z| ≤ model.u * |z| := by
  obtain ⟨δ, hδ, hz⟩ := model.round_spec z
  calc
    |model.round z - z| = |z| * |δ| := by
      rw [hz, show z * (1 + δ) - z = z * δ by ring, abs_mul]
    _ ≤ |z| * model.u := mul_le_mul_of_nonneg_left hδ (abs_nonneg z)
    _ = model.u * |z| := mul_comm _ _

theorem round_reference_error (model : Model) (z w : ℝ) :
    |model.round z - w| ≤ model.u * |w| + (1 + model.u) * |z - w| := by
  have hz : |z| ≤ |w| + |z - w| := by
    calc
      |z| = |w + (z - w)| := by congr 1; ring
      _ ≤ |w| + |z - w| := abs_add_le _ _
  calc
    |model.round z - w| = |(model.round z - z) + (z - w)| := by
      congr 1; ring
    _ ≤ |model.round z - z| + |z - w| := abs_add_le _ _
    _ ≤ model.u * |z| + |z - w| := add_le_add (round_error model z) le_rfl
    _ ≤ model.u * (|w| + |z - w|) + |z - w| :=
      add_le_add (mul_le_mul_of_nonneg_left hz model.u_nonneg) le_rfl
    _ = model.u * |w| + (1 + model.u) * |z - w| := by ring

/-- Forward error for every relative-error model, every finite coefficient
list, and every real argument. All rounding assumptions are fields of `model`;
no smallness, sign, nonzero-input, or exact-arithmetic assumptions are needed. -/
theorem forward_error (model : Model) (coefficients : List ℝ) (x : ℝ) :
    |Q model coefficients x - P coefficients x| ≤ E coefficients x model.u := by
  have hu : 0 ≤ 1 + model.u := by linarith [model.u_nonneg]
  induction coefficients with
  | nil => simp
  | cons a tail ih =>
    have hp : |model.round (x * Q model tail x) - x * P tail x| ≤
        model.u * |x * P tail x| + (1 + model.u) * |x| * E tail x model.u := by
      calc
        |model.round (x * Q model tail x) - x * P tail x| ≤
            model.u * |x * P tail x| +
              (1 + model.u) * |x * Q model tail x - x * P tail x| :=
          round_reference_error model _ _
        _ = model.u * |x * P tail x| +
              ((1 + model.u) * |x|) * |Q model tail x - P tail x| := by
          rw [← mul_sub x (Q model tail x) (P tail x)]
          simp only [abs_mul]
          ring
        _ ≤ model.u * |x * P tail x| +
              (1 + model.u) * |x| * E tail x model.u :=
          add_le_add le_rfl
            (mul_le_mul_of_nonneg_left ih (mul_nonneg hu (abs_nonneg x)))
    rw [Q_cons, P_cons, E_cons]
    calc
      _ ≤ model.u * |a + x * P tail x| +
          (1 + model.u) *
            |(a + model.round (x * Q model tail x)) - (a + x * P tail x)| :=
        round_reference_error model _ _
      _ = model.u * |a + x * P tail x| +
          (1 + model.u) * |model.round (x * Q model tail x) - x * P tail x| := by
        congr 2
        congr 1
        ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hu)

end Research.FloatingPoint.Horner

#print axioms Research.FloatingPoint.Horner.forward_error
#check Research.FloatingPoint.Horner.forward_error
