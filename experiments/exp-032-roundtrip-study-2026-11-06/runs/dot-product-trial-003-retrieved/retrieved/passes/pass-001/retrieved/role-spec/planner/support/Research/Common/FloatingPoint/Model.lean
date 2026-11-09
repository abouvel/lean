import Mathlib

/-!
# Abstract floating-point model

This is the standard relative-error model used by the binary-tree project,
not a bit-level formalization of IEEE 754.
-/

namespace Research.FloatingPoint

/-- A rounding operation satisfying the standard relative-error model.
The specification covers operations for which overflow and underflow do not occur.
-/
structure Model where
  u : ℝ
  u_nonneg : 0 ≤ u
  round : ℝ → ℝ
  round_spec : ∀ z : ℝ, ∃ δ : ℝ, |δ| ≤ u ∧ round z = z * (1 + δ)

/-- Floating-point addition induced by an abstract rounding model. -/
def Model.add (model : Model) (a b : ℝ) : ℝ :=
  model.round (a + b)

/-- Floating-point multiplication induced by an abstract rounding model. -/
def Model.mul (model : Model) (a b : ℝ) : ℝ :=
  model.round (a * b)

end Research.FloatingPoint
