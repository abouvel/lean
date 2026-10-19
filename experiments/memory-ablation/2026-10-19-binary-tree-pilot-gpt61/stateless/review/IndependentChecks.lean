import Research.Submission
open Bhola

-- Every expected stage is checked against the actual numerical definition.
example : stagesValues (· + ·) 0 [2,3,4,5,6] = [2,3,4,5,6] := rfl
example : stagesValues (· + ·) 1 [2,3,4,5,6] = [7,9,4] := by
  norm_num [stagesValues, roundValues, pairValues]
example : stagesValues (· + ·) 2 [2,3,4,5,6] = [11,9] := by
  norm_num [stagesValues, roundValues, pairValues]
example : stagesValues (· + ·) 3 [2,3,4,5,6] = [20] := by
  norm_num [stagesValues, roundValues, pairValues]
example : depth 5 = 3 := by native_decide

-- Arbitrary operations prevent exact addition from masking wrong pairing/carrying.
example (f : ℝ → ℝ → ℝ) (a b c d e : ℝ) :
    roundValues f [a,b,c,d,e] = [f a d, f b e, c] := by simp [roundValues, pairValues]
example (f : ℝ → ℝ → ℝ) (a b c d e : ℝ) :
    stagesValues f 3 [a,b,c,d,e] = [f (f (f a d) c) (f b e)] := by simp [roundValues, pairValues, stagesValues]
example (f : ℝ → ℝ → ℝ) (a b c : ℝ) :
    stagesValues f 2 [a,b,c] = [f (f a c) b] := by simp [roundValues, pairValues, stagesValues]
example (f : ℝ → ℝ → ℝ) (x : ℝ) : algorithm f [x] = x := by
  have h : depth 1 = 0 := by native_decide
  simp [algorithm, h, stagesValues]
example (a b c : Bhola.Tree) : round [a,b,c] = [Bhola.Tree.node a c,b] := by simp [Bhola.round, pair]
example (a b c d e : Bhola.Tree) :
    round [a,b,c,d,e] = [Bhola.Tree.node a d,Bhola.Tree.node b e,c] := by simp [Bhola.round, pair]
example (x : ℝ) : stagesValues (· + ·) 3 [x,x,x,x,x] = [5*x] := by
  simp [stagesValues, roundValues, pairValues]
  ring

-- The local model is satisfiable, and assumes local arithmetic, not the result.
example (u : ℝ) (hu : 0 ≤ u) : RoundingModel (· + ·) u := by
  intro a b
  exact ⟨0, by simpa, by ring⟩

-- Independent coordinatewise lifting for an arbitrary collection of coordinates.
theorem coordinatewise_check {ι : Type*} (xs : List (ι → ℝ))
    (hn : xs ≠ []) (f : ι → ℝ → ℝ → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hm : ∀ j, ExecutionModel (f j) u (xs.map (fun x => x j)))
    (hd : (depth xs.length : ℝ) * u < 1) :
    ∀ j, ∃ Δ : Fin (xs.map (fun x => x j)).length → ℝ,
      algorithm (f j) (xs.map (fun x => x j)) =
        ∑ i : Fin (xs.map (fun x => x j)).length, ((xs.map (fun x => x j)).get i + Δ i) ∧
      ∀ i, |Δ i| ≤ gamma (depth xs.length) u * |(xs.map (fun x => x j)).get i| := by
  intro j
  have hn' : xs.map (fun x => x j) ≠ [] := by simpa using hn
  have h := theorem_3_1 (f j) (xs.map (fun x => x j)) hn' hu (hm j)
    (by simpa using hd)
  simpa using h

#print axioms Bhola.theorem_3_1
#print axioms Bhola.algorithm1_spec
#print axioms Bhola.algorithm_exact
#print axioms coordinatewise_check
