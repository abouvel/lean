import Research.Common.FloatingPoint.Model

/-!
# Rounded Horner evaluation

The coefficient list is in increasing degree order. These constructions and
the theorem below follow `/spec/source.txt` directly.

Statement revision record: this is the initial statement; no feedback file
was present at formalization time. No additional assumptions are imposed.
-/

namespace Research.Horner

/-- Exact Horner evaluation, with the head coefficient as the constant term. -/
def P : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: tail, x => a + x * P tail x

/-- Horner evaluation with one rounded multiplication and one rounded addition
at every list step, using the supplied relative-error model. -/
def Q (model : Research.FloatingPoint.Model) : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: tail, x => model.round (a + model.round (x * Q model tail x))

/-- The prescribed forward-error envelope; it depends only on the exact
evaluation, coefficients, evaluation point, and error parameter. -/
def E : List ℝ → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | a :: tail, x, u =>
      let v := P tail x
      let e := E tail x u
      u * |a + x * v| + (1 + u) * (u * |x * v| + (1 + u) * |x| * e)

lemma rounding_error (model : Research.FloatingPoint.Model) (z : ℝ) :
    |model.round z - z| ≤ model.u * |z| := by
  obtain ⟨δ, hδ, hr⟩ := model.round_spec z
  calc
    |model.round z - z| = |z * δ| := by rw [hr]; congr 1; ring
    _ = |z| * |δ| := abs_mul z δ
    _ ≤ |z| * model.u := mul_le_mul_of_nonneg_left hδ (abs_nonneg z)
    _ = model.u * |z| := mul_comm _ _

lemma rounding_perturbation (model : Research.FloatingPoint.Model) (z t : ℝ) :
    |model.round z - t| ≤ model.u * |t| + (1 + model.u) * |z - t| := by
  have hz : |z| ≤ |t| + |z - t| := by
    calc
      |z| = |t + (z - t)| := by congr 1 <;> ring
      _ ≤ |t| + |z - t| := abs_add_le _ _
  calc
    |model.round z - t| = |(model.round z - z) + (z - t)| := by
      congr 1 <;> ring
    _ ≤ |model.round z - z| + |z - t| := abs_add_le _ _
    _ ≤ model.u * |z| + |z - t| := add_le_add (rounding_error model z) le_rfl
    _ ≤ model.u * (|t| + |z - t|) + |z - t| :=
      add_le_add (mul_le_mul_of_nonneg_left hz model.u_nonneg) le_rfl
    _ = model.u * |t| + (1 + model.u) * |z - t| := by ring

/-- Universal forward-error bound. Nonnegativity of `model.u` and the relative
rounding law are exactly the fields of the supplied model; no smallness,
sign, nonzero-input, or exact-arithmetic assumptions are needed. -/
theorem forward_error (model : Research.FloatingPoint.Model)
    (coefficients : List ℝ) (x : ℝ) :
    |Q model coefficients x - P coefficients x| ≤ E coefficients x model.u := by
  induction coefficients with
  | nil => simp [Q, P, E]
  | cons a tail ih =>
      have hu : 0 ≤ 1 + model.u := by linarith [model.u_nonneg]
      have hm : |x * Q model tail x - x * P tail x| ≤ |x| * E tail x model.u := by
        calc
          |x * Q model tail x - x * P tail x| = |x * (Q model tail x - P tail x)| := by
            congr 1 <;> ring
          _ = |x| * |Q model tail x - P tail x| := abs_mul _ _
          _ ≤ |x| * E tail x model.u := mul_le_mul_of_nonneg_left ih (abs_nonneg x)
      have hi : |model.round (x * Q model tail x) - x * P tail x| ≤
          model.u * |x * P tail x| + (1 + model.u) * |x| * E tail x model.u := by
        calc
          _ ≤ model.u * |x * P tail x| +
              (1 + model.u) * |x * Q model tail x - x * P tail x| :=
            rounding_perturbation model _ _
          _ ≤ model.u * |x * P tail x| +
              (1 + model.u) * (|x| * E tail x model.u) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hm hu)
          _ = _ := by ring
      change |model.round (a + model.round (x * Q model tail x)) - (a + x * P tail x)| ≤ _
      calc
        _ ≤ model.u * |a + x * P tail x| +
            (1 + model.u) * |(a + model.round (x * Q model tail x)) - (a + x * P tail x)| :=
          rounding_perturbation model _ _
        _ = model.u * |a + x * P tail x| +
            (1 + model.u) * |model.round (x * Q model tail x) - x * P tail x| := by
          rw [add_sub_add_left_eq_sub]
        _ ≤ model.u * |a + x * P tail x| + (1 + model.u) *
            (model.u * |x * P tail x| + (1 + model.u) * |x| * E tail x model.u) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hi hu)
        _ = E (a :: tail) x model.u := rfl

end Research.Horner
