import Research.Common.FloatingPoint.Model

/-!
# Rounded Horner evaluation

Coefficients are listed in increasing degree order. The model's fields
`u_nonneg` and `round_spec` are the only rounding assumptions used in the
forward-error statement. There are no restrictions on coefficients or x.

Statement audit: /spec/source.txt is the source of the recurrences and bound.
No /spec/feedback.json was present; no statement revision was required.
-/

namespace Research.Horner

open Research.FloatingPoint

/-- Exact Horner evaluation of coefficients in increasing degree order. -/
def P : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: tail, x => a + x * P tail x

/-- Rounded Horner evaluation, with one rounded multiplication and one rounded
addition at every coefficient, including the final list step. -/
def Q (model : Model) : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: tail, x => model.round (a + model.round (x * Q model tail x))

/-- The prescribed forward-error envelope, depending only on exact data and u. -/
def E : List ℝ → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | a :: tail, x, u =>
      let v := P tail x
      let e := E tail x u
      u * |a + x * v| + (1 + u) * (u * |x * v| + (1 + u) * |x| * e)

/-- Rounding error measured against an arbitrary exact reference. -/
lemma round_reference (model : Model) (z t : ℝ) :
    |model.round z - t| ≤ model.u * |t| + (1 + model.u) * |z - t| := by
  obtain ⟨δ, hδ, hr⟩ := model.round_spec z
  have hlocal : |model.round z - z| ≤ model.u * |z| := by
    rw [hr, show z * (1 + δ) - z = z * δ by ring, abs_mul]
    calc
      |z| * |δ| ≤ |z| * model.u := mul_le_mul_of_nonneg_left hδ (abs_nonneg z)
      _ = model.u * |z| := by ring
  have hz : |z| ≤ |t| + |z - t| := by
    calc
      |z| = |t + (z - t)| := by congr 1; ring
      _ ≤ |t| + |z - t| := abs_add_le _ _
  calc
    |model.round z - t| = |(model.round z - z) + (z - t)| := by congr 1; ring
    _ ≤ |model.round z - z| + |z - t| := abs_add_le _ _
    _ ≤ model.u * |z| + |z - t| := add_le_add hlocal (le_refl _)
    _ ≤ model.u * (|t| + |z - t|) + |z - t| :=
      add_le_add (mul_le_mul_of_nonneg_left hz model.u_nonneg) (le_refl _)
    _ = model.u * |t| + (1 + model.u) * |z - t| := by ring

/-- For every abstract relative-error model, every finite coefficient list,
and every real input, the prescribed envelope bounds the absolute forward
error. Nonnegativity of u and the relative rounding law are supplied by Model;
no smallness, sign, nonzero-input, or exact-arithmetic assumptions are needed. -/
theorem forward_error (model : Model) (coefficients : List ℝ) (x : ℝ) :
    |Q model coefficients x - P coefficients x| ≤ E coefficients x model.u := by
  induction coefficients with
  | nil => simp [Q, P, E]
  | cons a tail ih =>
    have hfactor : 0 ≤ 1 + model.u := by linarith [model.u_nonneg]
    have hmul : |x * Q model tail x - x * P tail x| ≤ |x| * E tail x model.u := by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left ih (abs_nonneg x)
    have hround : |model.round (x * Q model tail x) - x * P tail x| ≤
        model.u * |x * P tail x| + (1 + model.u) * |x| * E tail x model.u := by
      calc
        _ ≤ model.u * |x * P tail x| +
            (1 + model.u) * |x * Q model tail x - x * P tail x| :=
          round_reference model _ _
        _ ≤ model.u * |x * P tail x| +
            (1 + model.u) * (|x| * E tail x model.u) :=
          add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hmul hfactor)
        _ = _ := by ring
    change |model.round (a + model.round (x * Q model tail x)) -
        (a + x * P tail x)| ≤ _
    calc
      _ ≤ model.u * |a + x * P tail x| + (1 + model.u) *
          |(a + model.round (x * Q model tail x)) - (a + x * P tail x)| :=
        round_reference model _ _
      _ = model.u * |a + x * P tail x| + (1 + model.u) *
          |model.round (x * Q model tail x) - x * P tail x| := by
        rw [add_sub_add_left_eq_sub]
      _ ≤ model.u * |a + x * P tail x| + (1 + model.u) *
          (model.u * |x * P tail x| + (1 + model.u) * |x| * E tail x model.u) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hround hfactor)
      _ = E (a :: tail) x model.u := rfl

end Research.Horner
