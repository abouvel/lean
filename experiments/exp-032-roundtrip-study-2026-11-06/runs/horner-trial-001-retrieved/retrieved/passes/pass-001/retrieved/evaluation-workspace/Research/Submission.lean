import Research.Common.FloatingPoint.Model

/-!
Rounded Horner evaluation for coefficients in increasing degree order.
The envelope uses exact evaluation and the parameter `u` only.
No feedback.json was supplied; no statement revision was required.
-/

namespace Research.Horner

/-- Exact Horner evaluation; the head coefficient is the constant term. -/
def P : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: tail, x => a + x * P tail x

/-- Horner evaluation with one rounded multiplication and one rounded addition
at each list step. -/
def Q (model : Research.FloatingPoint.Model) : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: tail, x => model.round (a + model.round (x * Q model tail x))

/-- The prescribed error envelope, independent of the rounding operation. -/
def E : List ℝ → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | a :: tail, x, u =>
      let v := P tail x
      let e := E tail x u
      u * |a + x * v| + (1 + u) * (u * |x * v| + (1 + u) * |x| * e)

/-- Rounding at a perturbed input, compared to an exact reference. -/
lemma rounding_perturbation (model : Research.FloatingPoint.Model) (y z : ℝ) :
    |model.round y - z| ≤ model.u * |z| + (1 + model.u) * |y - z| := by
  obtain ⟨δ, hδ, hr⟩ := model.round_spec y
  have herr : |model.round y - y| ≤ model.u * |y| := by
    rw [hr, show y * (1 + δ) - y = y * δ by ring, abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hδ (abs_nonneg y)]
  have hy : |y| ≤ |z| + |y - z| := by
    calc
      |y| = |z + (y - z)| := by congr 1; ring
      _ ≤ |z| + |y - z| := abs_add_le _ _
  calc
    |model.round y - z| = |(model.round y - y) + (y - z)| := by congr 1; ring
    _ ≤ |model.round y - y| + |y - z| := abs_add_le _ _
    _ ≤ model.u * |y| + |y - z| := add_le_add herr (le_refl _)
    _ ≤ model.u * (|z| + |y - z|) + |y - z| :=
      add_le_add (mul_le_mul_of_nonneg_left hy model.u_nonneg) (le_refl _)
    _ = model.u * |z| + (1 + model.u) * |y - z| := by ring

/-- Universal forward-error bound in the supplied relative-error model.
Nonnegativity of `model.u` and the relative rounding law are fields of `model`;
there are no further assumptions on the coefficients, `x`, or `model.u`. -/
theorem forward_error_bound (model : Research.FloatingPoint.Model)
    (coefficients : List ℝ) (x : ℝ) :
    |Q model coefficients x - P coefficients x| ≤ E coefficients x model.u := by
  have hu : 0 ≤ 1 + model.u := by linarith [model.u_nonneg]
  induction coefficients with
  | nil => simp [Q, P, E]
  | cons a tail ih =>
    have hm : |model.round (x * Q model tail x) - x * P tail x| ≤
        model.u * |x * P tail x| + (1 + model.u) * |x| * E tail x model.u := by
      calc
        _ ≤ model.u * |x * P tail x| +
            (1 + model.u) * |x * Q model tail x - x * P tail x| :=
          rounding_perturbation model _ _
        _ = model.u * |x * P tail x| +
            (1 + model.u) * |x| * |Q model tail x - P tail x| := by
          rw [← mul_sub]
          simp only [abs_mul, mul_assoc]
        _ ≤ _ := add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left ih (mul_nonneg hu (abs_nonneg x)))
    change |model.round (a + model.round (x * Q model tail x)) -
        (a + x * P tail x)| ≤ _
    calc
      _ ≤ model.u * |a + x * P tail x| + (1 + model.u) *
          |(a + model.round (x * Q model tail x)) - (a + x * P tail x)| :=
        rounding_perturbation model _ _
      _ = model.u * |a + x * P tail x| + (1 + model.u) *
          |model.round (x * Q model tail x) - x * P tail x| := by
        rw [add_sub_add_left_eq_sub]
      _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hm hu)

end Research.Horner
