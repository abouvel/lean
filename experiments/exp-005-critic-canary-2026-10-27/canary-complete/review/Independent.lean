import Research.Submission
open Bhola

example : roundValues (· + ·) [2,3,4,5,6] = ([7,9,4] : List ℝ) := by
  norm_num [roundValues, pairValues]
example : roundValues (· + ·) [7,9,4] = ([11,9] : List ℝ) := by
  norm_num [roundValues, pairValues]
example : roundValues (· + ·) [11,9] = ([20] : List ℝ) := by
  norm_num [roundValues, pairValues]
example : depth 5 = 3 := by native_decide
example : depth 1 = 0 := by native_decide
example (add : ℝ → ℝ → ℝ) (x : ℝ) : algorithm add [x] = x := by
  simp [algorithm, depth, Nat.clog, stagesValues]
example : roundValues (fun a b => a + b + 1) [2,3,4,5,6] =
    ([8,10,4] : List ℝ) := by
  norm_num [roundValues, pairValues]
example : roundValues (· + ·) [2,2,2] = ([4,2] : List ℝ) := by
  norm_num [roundValues, pairValues]
example : stagesValues (· + ·) 2 [2,2,2] = ([6] : List ℝ) := by
  norm_num [stagesValues, roundValues, pairValues]
example : stagesValues (· + ·) 3 [2,3,4,5,6] = ([20] : List ℝ) := by
  norm_num [stagesValues, roundValues, pairValues]

-- Scalar result simultaneously instantiated for arbitrary components.
theorem componentwise_check {ι : Type*} (xs : List (ι → ℝ))
    (hn : xs ≠ []) (add : ι → ℝ → ℝ → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hm : ∀ j, ExecutionModel (add j) u (xs.map (fun x => x j)))
    (hd : (depth xs.length : ℝ) * u < 1) :
    ∃ zs : ι → List ℝ, ∀ j,
      List.Forall₂ (fun x z => |z - x| ≤ gamma (depth xs.length) u * |x|)
        (xs.map (fun x => x j)) (zs j) ∧
      algorithm (add j) (xs.map (fun x => x j)) = (zs j).sum := by
  classical
  have h : ∀ j : ι, ∃ zs : List ℝ,
      List.Forall₂ (fun x z => |z - x| ≤ gamma (depth xs.length) u * |x|)
        (xs.map (fun x => x j)) zs ∧
      algorithm (add j) (xs.map (fun x => x j)) = zs.sum := by
    intro j
    simpa only [List.length_map] using
      theorem_3_1_list_local (add j) (xs.map (fun x => x j))
        (by simpa using hn) hu (hm j) (by simpa using hd)
  exact Classical.skolem.mp h

#print axioms Bhola.theorem_3_1
#print axioms Bhola.algorithm1_spec
#print axioms Bhola.stage_offset
#print axioms componentwise_check
