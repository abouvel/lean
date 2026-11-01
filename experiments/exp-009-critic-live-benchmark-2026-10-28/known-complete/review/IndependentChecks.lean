import Research.Submission

open Bhola

#print axioms Bhola.theorem_3_1
#print axioms Bhola.algorithm1_spec
#print axioms Bhola.stage_offset
#print axioms Bhola.algorithm_exact

example : roundValues (· + ·) ([2,3,4,5,6] : List ℝ) = [7,9,4] := by
  norm_num [roundValues, pairValues]
example : roundValues (· + ·) ([7,9,4] : List ℝ) = [11,9] := by
  norm_num [roundValues, pairValues]
example : roundValues (· + ·) ([11,9] : List ℝ) = [20] := by
  norm_num [roundValues, pairValues]

-- A nonassociative operation detects both the pairing order and a spurious carry call.
example : roundValues (fun a b => 10*a+b+100) ([2,3,4,5,6] : List ℝ) =
    [125,136,4] := by
  norm_num [roundValues, pairValues]
example : roundValues (fun a b => 10*a+b+100) ([7] : List ℝ) = [7] := by
  norm_num [roundValues, pairValues]
example : roundValues (· + ·) ([2,2,2,2,2] : List ℝ) = [4,4,2] := by
  norm_num [roundValues, pairValues]

example : depth 1 = 0 ∧ depth 3 = 2 ∧ depth 5 = 3 ∧ depth 8 = 3 ∧ depth 9 = 4 := by
  decide

example (add : ℝ → ℝ → ℝ) (x : ℝ) : algorithm add [x] = x := by
  simp [algorithm, depth, Nat.clog, stagesValues]

example : algorithm (· + ·) ([2,2,2,2,2] : List ℝ) = 10 := by
  rw [algorithm_exact _ (by simp)]
  norm_num

example (add : ℝ → ℝ → ℝ) (xs : List ℝ) (hne : xs ≠ [])
    (u : ℝ) (hu : 0 ≤ u) (hm : ExecutionModel add u xs)
    (hd : (Nat.clog 2 xs.length : ℝ) * u < 1) :
    ∃ Δ : Fin xs.length → ℝ,
      algorithm add xs = ∑ i : Fin xs.length, (xs.get i + Δ i) ∧
      ∀ i, |Δ i| ≤ ((Nat.clog 2 xs.length : ℝ) * u /
        (1 - (Nat.clog 2 xs.length : ℝ) * u)) * |xs.get i| := by
  exact theorem_3_1 add xs hne hu hm hd
