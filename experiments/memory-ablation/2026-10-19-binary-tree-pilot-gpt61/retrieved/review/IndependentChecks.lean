import Research
open Bhola
noncomputable section
namespace IndependentReview

def sample : List ℝ := [2,3,4,5,6]
def exactAdd : ℕ → ℕ → ℝ → ℝ → ℝ := fun _ _ a b => a+b

example : (forest (fun _ _ => 0) sample 0).map Tree.eval = [2,3,4,5,6] := by
  norm_num [forest, sample, Tree.eval]
example : (forest (fun _ _ => 0) sample 1).map Tree.eval = [7,9,4] := by
  norm_num [forest, sample, Bhola.round, pair, half, Tree.eval]
example : (forest (fun _ _ => 0) sample 2).map Tree.eval = [11,9] := by
  norm_num [forest, sample, Bhola.round, pair, half, Tree.eval]
example : (forest (fun _ _ => 0) sample 3).map Tree.eval = [20] := by
  norm_num [forest, sample, Bhola.round, pair, half, Tree.eval]
example : depth sample = 3 := by decide
example : [run exactAdd sample 1 0, run exactAdd sample 1 1,
    run exactAdd sample 1 2] = [7,9,4] := by
  norm_num [run, exactAdd, sample, width, Nat.ceilDiv_eq_add_pred_div]
example : [run exactAdd sample 2 0, run exactAdd sample 2 1] = [11,9] := by
  norm_num [run, exactAdd, sample, width, Nat.ceilDiv_eq_add_pred_div]
example : run exactAdd sample 3 0 = 20 := by
  norm_num [run, exactAdd, sample, width, Nat.ceilDiv_eq_add_pred_div]

-- Carry a composite subtree, with an arbitrary oracle: structural equality.
example (δ : ℕ → ℝ) (e a b c d : ℝ) :
    round δ [Tree.leaf a, Tree.add e (.leaf b) (.leaf c), Tree.leaf d] =
      [Tree.add (δ 0) (.leaf a) (.leaf d), Tree.add e (.leaf b) (.leaf c)] := by
  norm_num [Bhola.round, pair, half]
example (fl : ℕ → ℕ → ℝ → ℝ → ℝ) :
    run fl sample 2 1 = run fl sample 1 1 := by
  norm_num [run, sample, width, Nat.ceilDiv_eq_add_pred_div]
example (fl : ℕ → ℕ → ℝ → ℝ → ℝ) (x : ℝ) : sumFP fl [x] = x := by
  have hd : depth [x] = 0 := by simp [depth]
  simp [sumFP, hd, run]
example : (forest (fun _ _ => 0) ([2,2,2] : List ℝ) 1).map Tree.eval = [4,2] := by
  norm_num [forest, Bhola.round, pair, half, Tree.eval]
example : (forest (fun _ _ => 0) ([2,2,2] : List ℝ) 2).map Tree.eval = [6] := by
  norm_num [forest, Bhola.round, pair, half, Tree.eval]
example : leaves (forest (fun _ _ => 0) ([2,2,2] : List ℝ) 2) = [2,2,2] := by
  norm_num [forest, Bhola.round, pair, half, leaves, Tree.leaves]
example : (forest (fun _ _ => 1) sample 1).map Tree.eval = [14,18,4] := by
  norm_num [forest, sample, Bhola.round, pair, half, Tree.eval]
example : (forest (fun _ _ => 1) sample 2).map Tree.eval = [36,18] := by
  norm_num [forest, sample, Bhola.round, pair, half, Tree.eval]

-- Instantiate the actual numerical theorem at nonzero roundoff and arbitrary inputs.
example (xs : List ℝ) (hne : xs ≠ [])
    (hd : (depth xs : ℝ) * (1/100) < 1) :
    ∃ Δ : Fin xs.length → ℝ,
      sumFP (fun _ _ a b => (a+b)*(1+1/100)) xs =
        ∑ i : Fin xs.length, (xs.get i + Δ i) ∧
      ∀ i, |Δ i| ≤ gamma (1/100) (depth xs) * |xs.get i| := by
  apply theorem_3_1_floatingPoint hne (by norm_num) ?_ hd
  intro d k _ _ _
  exact ⟨1/100, by norm_num, rfl⟩

#print axioms Bhola.algorithm1_theorem3_1
#print axioms Bhola.round_getD
#print axioms Bhola.exact_depth
#print axioms Bhola.sumFP_exact
end IndependentReview
