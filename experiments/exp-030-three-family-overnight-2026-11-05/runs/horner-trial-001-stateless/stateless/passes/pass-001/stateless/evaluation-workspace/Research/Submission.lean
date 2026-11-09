import Research.Common.FloatingPoint.Model

/-!
# Rounded Horner evaluation

Coefficients are listed in increasing degree order. Each nonempty step of
`Q` performs one rounded multiplication and one rounded addition, even for
singleton coefficient lists. `E` depends only on exact evaluation and `u`.

Statement revision record: initial formalization of `/spec/source.txt`;
no `/spec/feedback.json` was present and no statement revisions were made.
The final theorem uses only the assumptions supplied by `Model`.
-/

namespace Research.FloatingPoint.Horner

/-- Exact Horner evaluation, with coefficients in increasing degree order. -/
def P : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: tail, x => a + x * P tail x

/-- Horner evaluation with exactly two rounding operations per list step. -/
def Q (model : Model) : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: tail, x => model.round (a + model.round (x * Q model tail x))

/-- The prescribed forward-error envelope, independent of rounded evaluation. -/
def E : List ℝ → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | a :: tail, x, u =>
      let v := P tail x
      let e := E tail x u
      u * |a + x * v| + (1 + u) * (u * |x * v| + (1 + u) * |x| * e)

lemma rounding_perturbation (model : Model) (z t : ℝ) :
    |model.round z - t| ≤ model.u * |t| + (1 + model.u) * |z - t| := by
  obtain ⟨δ, hδ, hz⟩ := model.round_spec z
  have hr : |model.round z - z| ≤ model.u * |z| := by
    rw [hz, show z * (1 + δ) - z = z * δ by ring, abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hδ (abs_nonneg z)]
  have habs : |z| ≤ |t| + |z - t| := by
    calc
      |z| = |t + (z - t)| := by congr 1; ring
      _ ≤ |t| + |z - t| := abs_add_le _ _
  calc
    |model.round z - t| = |(model.round z - z) + (z - t)| := by congr 1; ring
    _ ≤ |model.round z - z| + |z - t| := abs_add_le _ _
    _ ≤ model.u * |z| + |z - t| := add_le_add hr le_rfl
    _ ≤ model.u * (|t| + |z - t|) + |z - t| :=
      add_le_add (mul_le_mul_of_nonneg_left habs model.u_nonneg) le_rfl
    _ = model.u * |t| + (1 + model.u) * |z - t| := by ring

/-- For every supplied relative-error rounding model, every coefficient list,
and every real input, the rounded Horner error is bounded by the prescribed
envelope. Nonnegativity of `model.u` and the relative rounding law are fields
of `Model`; no additional assumptions are required. -/
theorem forward_error (model : Model) (coefficients : List ℝ) (x : ℝ) :
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
            (1 + model.u) * (|x| * |Q model tail x - P tail x|) := by
          rw [← mul_sub]
          simp only [abs_mul]
        _ ≤ model.u * |x * P tail x| +
            (1 + model.u) * (|x| * E tail x model.u) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left ih (abs_nonneg x)) hu)
        _ = _ := by ring
    change |model.round (a + model.round (x * Q model tail x)) -
      (a + x * P tail x)| ≤ _
    calc
      _ ≤ model.u * |a + x * P tail x| + (1 + model.u) *
          |(a + model.round (x * Q model tail x)) - (a + x * P tail x)| :=
        rounding_perturbation model _ _
      _ = model.u * |a + x * P tail x| + (1 + model.u) *
          |model.round (x * Q model tail x) - x * P tail x| := by
        rw [add_sub_add_left_eq_sub]
      _ ≤ model.u * |a + x * P tail x| + (1 + model.u) *
          (model.u * |x * P tail x| + (1 + model.u) * |x| * E tail x model.u) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hm hu)
      _ = E (a :: tail) x model.u := rfl

end Research.FloatingPoint.Horner
