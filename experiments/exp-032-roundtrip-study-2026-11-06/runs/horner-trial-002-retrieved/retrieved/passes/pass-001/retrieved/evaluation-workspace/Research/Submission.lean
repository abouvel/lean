import Research.Common.FloatingPoint.Model

/-!
Rounded Horner evaluation for coefficients in increasing degree order.
The statement follows /spec/source.txt. No feedback.json was supplied;
no statement revision was made from feedback.
-/

namespace Research.FloatingPoint.Horner

/-- Exact Horner evaluation, with the constant coefficient first. -/
def P : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: tail, x => a + x * P tail x

/-- Horner evaluation with one rounded product and one rounded sum per step. -/
def Q (model : Model) : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: tail, x => model.round (a + model.round (x * Q model tail x))

/-- The prescribed forward-error envelope, depending only on exact data. -/
def E : List ℝ → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | a :: tail, x, u =>
      u * |a + x * P tail x| +
        (1 + u) * (u * |x * P tail x| + (1 + u) * |x| * E tail x u)

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

/-- Forward error for every supplied relative-error model, coefficient list,
and real input. Nonnegativity of `model.u` and the relative rounding law
are fields of `Model`; there are no additional hypotheses. -/
theorem forward_error (model : Model) (coefficients : List ℝ) (x : ℝ) :
    |Q model coefficients x - P coefficients x| ≤ E coefficients x model.u := by
  have round_error (z : ℝ) : |model.round z - z| ≤ model.u * |z| := by
    obtain ⟨δ, hδ, hr⟩ := model.round_spec z
    rw [hr, show z * (1 + δ) - z = δ * z by ring, abs_mul]
    exact mul_le_mul_of_nonneg_right hδ (abs_nonneg z)
  have perturb (z w : ℝ) :
      |model.round z - w| ≤ model.u * |w| + (1 + model.u) * |z - w| := by
    have hz : |z| ≤ |w| + |z - w| := by
      calc
        |z| = |w + (z - w)| := by congr 1; ring
        _ ≤ |w| + |z - w| := abs_add_le _ _
    calc
      |model.round z - w| = |(model.round z - z) + (z - w)| := by
        congr 1; ring
      _ ≤ |model.round z - z| + |z - w| := abs_add_le _ _
      _ ≤ model.u * |z| + |z - w| := add_le_add (round_error z) (le_refl _)
      _ ≤ model.u * (|w| + |z - w|) + |z - w| :=
        add_le_add (mul_le_mul_of_nonneg_left hz model.u_nonneg) (le_refl _)
      _ = model.u * |w| + (1 + model.u) * |z - w| := by ring
  have hu : 0 ≤ 1 + model.u := by linarith [model.u_nonneg]
  induction coefficients with
  | nil => simp
  | cons a tail ih =>
    have hp : |x * Q model tail x - x * P tail x| ≤
        |x| * E tail x model.u := by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left ih (abs_nonneg x)
    have hm : |model.round (x * Q model tail x) - x * P tail x| ≤
        model.u * |x * P tail x| +
          (1 + model.u) * |x| * E tail x model.u := by
      calc
        _ ≤ model.u * |x * P tail x| +
            (1 + model.u) * |x * Q model tail x - x * P tail x| := perturb _ _
        _ ≤ model.u * |x * P tail x| +
            (1 + model.u) * (|x| * E tail x model.u) :=
          add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hp hu)
        _ = _ := by ring
    simp only [Q_cons, P_cons, E_cons]
    calc
      _ ≤ model.u * |a + x * P tail x| + (1 + model.u) *
          |(a + model.round (x * Q model tail x)) - (a + x * P tail x)| :=
        perturb _ _
      _ = model.u * |a + x * P tail x| + (1 + model.u) *
          |model.round (x * Q model tail x) - x * P tail x| := by
        rw [add_sub_add_left_eq_sub]
      _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hm hu)

end Research.FloatingPoint.Horner
