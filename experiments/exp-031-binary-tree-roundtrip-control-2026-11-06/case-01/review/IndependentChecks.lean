import Research.Submission
open Bhola

-- The evaluator's full acceptance trace.
example : stagesValues (· + ·) 0 [2,3,4,5,6] = [2,3,4,5,6] := by rfl
example : stagesValues (· + ·) 1 [2,3,4,5,6] = [7,9,4] := by
  norm_num [stagesValues, roundValues, pairValues]
example : stagesValues (· + ·) 2 [2,3,4,5,6] = [11,9] := by
  norm_num [stagesValues, roundValues, pairValues]
example : stagesValues (· + ·) 3 [2,3,4,5,6] = [20] := by
  norm_num [stagesValues, roundValues, pairValues]

-- A deliberately inexact operation detects arithmetic on a carried entry.
example : roundValues (fun a b => a + b + 1) [2,3,4,5,6] = [8,10,4] := by
  norm_num [roundValues, pairValues]
example : roundValues (fun a b => a + b + 1) [7,9,4] = [12,9] := by
  norm_num [roundValues, pairValues]
example (add : ℝ → ℝ → ℝ) (x : ℝ) : algorithm add [x] = x := by
  simp [algorithm, depth, Nat.clog, stagesValues]
example : stagesValues (· + ·) 3 [2,2,2,2,2] = [10] := by
  norm_num [stagesValues, roundValues, pairValues]

-- The target can be instantiated with a nonvacuous execution model.
example (xs : List ℝ) (hn : xs ≠ []) :
    ∃ Δ : Fin xs.length → ℝ,
      algorithm (· + ·) xs = ∑ i : Fin xs.length, (xs.get i + Δ i) ∧
      ∀ i, |Δ i| ≤ gamma (depth xs.length) 0 * |xs.get i| := by
  apply theorem_3_1_global (· + ·) xs hn (by norm_num)
  · intro a b
    exact ⟨0, by norm_num, by ring⟩
  · simp

#print axioms Bhola.theorem_3_1
#print axioms Bhola.algorithm1_spec
#print axioms Bhola.depth_spec
