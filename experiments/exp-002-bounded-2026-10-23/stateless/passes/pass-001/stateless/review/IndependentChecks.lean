import Research.Submission
open Bhola

-- Requested acceptance trace, checked by the kernel.
example : levels (· + ·) 0 ([2,3,4,5,6] : List Nat) = [2,3,4,5,6] := rfl
example : levels (· + ·) 1 ([2,3,4,5,6] : List Nat) = [7,9,4] := by decide
example : levels (· + ·) 2 ([2,3,4,5,6] : List Nat) = [11,9] := by decide
example : levels (· + ·) 3 ([2,3,4,5,6] : List Nat) = [20] := by decide
example : depth 5 = 3 := by decide
example : depth 1 = 0 := by decide
example : levels (· + ·) 3 ([1,1,1,1,1] : List Nat) = [5] := by decide
example : levels (· + ·) 2 ([2,3,4] : List Nat) = [9] := by decide
-- A marked operation exposes an erroneous extra operation on a carry.
example : round (fun a b : Nat => a + b + 100) [2,3,4,5,6] = [107,109,4] := by decide
example : round (fun a b : Nat => a + b + 100) [7] = [7] := by decide
-- Carry preserves an entire symbolic subtree, not merely its evaluated value.
example (op : α → α → α) (a b c d e : α) :
    round op [a,b,c,d,e] = [op a d, op b e, c] := by simp [Bhola.round, Bhola.pair]
example (op : α → α → α) (a : α) : round op [a] = [a] := by simp [Bhola.round, Bhola.pair]
example (add : ℝ → ℝ → ℝ) (a : ℝ) : algorithm add [a] = [a] := rfl
example : levels (· ++ ·) 3 ([[0],[1],[2],[3],[4]] : List (List Nat)) =
    [[0,3,2,1,4]] := by decide
example : levels (· ++ ·) 3 ([[1],[1],[1],[1],[1]] : List (List Nat)) =
    [[1,1,1,1,1]] := by decide
#print axioms Bhola.algorithm_length
#print axioms Bhola.exact_sum
#print axioms Bhola.singleton_occurrences
#print axioms Bhola.depth_minimal
#print axioms Bhola.path_error
#check Bhola.StandardModel
#check Bhola.BackwardStable
