import Research.Common.FloatingPoint.Model

namespace Research.Horner

/-- Exact Horner evaluation of coefficients in increasing degree order. -/
def P : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: tail, x => a + x * P tail x

/-- Horner evaluation with one rounded multiplication and one rounded addition
at every list step, including the last coefficient. -/
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

/-- Rounding error relative to an arbitrary exact reference. -/
lemma rounding_perturbation_bound (model : Research.FloatingPoint.Model)
    (z t : ℝ) :
    |model.round z - t| ≤ model.u * |t| + (1 + model.u) * |z - t| := by
  obtain ⟨δ, hδ, hr⟩ := model.round_spec z
  have herr : |model.round z - z| ≤ model.u * |z| := by
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
    _ ≤ model.u * |z| + |z - t| := add_le_add herr le_rfl
    _ ≤ model.u * (|t| + |z - t|) + |z - t| :=
      add_le_add (mul_le_mul_of_nonneg_left hz model.u_nonneg) le_rfl
    _ = model.u * |t| + (1 + model.u) * |z - t| := by ring

/-- Forward error for every supplied relative-error model, every finite list
of real coefficients, and every real evaluation point. Nonnegativity of `u`
and the relative rounding law are fields of `model`; no other assumptions
are required. -/
theorem forward_error (model : Research.FloatingPoint.Model)
    (coefficients : List ℝ) (x : ℝ) :
    |Q model coefficients x - P coefficients x| ≤ E coefficients x model.u := by
  induction coefficients with
  | nil => simp [Q, P, E]
  | cons a tail ih =>
    have hu : 0 ≤ 1 + model.u := by linarith [model.u_nonneg]
    have hmul :
        |model.round (x * Q model tail x) - x * P tail x| ≤
          model.u * |x * P tail x| + (1 + model.u) * |x| * E tail x model.u := by
      calc
        _ ≤ model.u * |x * P tail x| +
            (1 + model.u) * |x * Q model tail x - x * P tail x| :=
          rounding_perturbation_bound model _ _
        _ = model.u * |x * P tail x| +
            ((1 + model.u) * |x|) * |Q model tail x - P tail x| := by
          rw [show x * Q model tail x - x * P tail x =
            x * (Q model tail x - P tail x) by ring]
          simp only [abs_mul]
          ring
        _ ≤ _ := add_le_add le_rfl
          (mul_le_mul_of_nonneg_left ih (mul_nonneg hu (abs_nonneg x)))
    change |model.round (a + model.round (x * Q model tail x)) -
        (a + x * P tail x)| ≤ _
    calc
      _ ≤ model.u * |a + x * P tail x| + (1 + model.u) *
          |(a + model.round (x * Q model tail x)) - (a + x * P tail x)| :=
        rounding_perturbation_bound model _ _
      _ = model.u * |a + x * P tail x| + (1 + model.u) *
          |model.round (x * Q model tail x) - x * P tail x| := by
        rw [show (a + model.round (x * Q model tail x)) - (a + x * P tail x) =
          model.round (x * Q model tail x) - x * P tail x by ring]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hmul hu)

end Research.Horner
