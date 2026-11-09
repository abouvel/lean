import Mathlib
namespace Research
theorem root_exists : ∃ x : ℝ, x * x = 0 := by
  exact ⟨0, by norm_num⟩
end Research
