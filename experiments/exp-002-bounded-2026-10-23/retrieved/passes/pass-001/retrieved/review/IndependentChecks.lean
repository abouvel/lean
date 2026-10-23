import Research.Submission
open Bhola

-- Exact acceptance levels and special cases, using the actual candidate definitions.
example : round Nat.add [2,3,4,5,6] = [7,9,4] := by decide
example : round Nat.add [7,9,4] = [11,9] := by decide
example : round Nat.add [11,9] = [20] := by decide
example : stages Nat.add (depth [2,3,4,5,6]) [2,3,4,5,6] = [20] := by decide
example : depth ([2,3,4,5,6] : List Nat) = 3 := by decide
example : stages Nat.add (depth [42]) [42] = [42] := by decide
example : depth ([42] : List Nat) = 0 := by decide
example : round Nat.add [1,2,3] = [4,2] := by decide
example : stages Nat.add (depth [1,2,3]) [1,2,3] = [6] := by decide
example : stages Nat.add (depth [2,2,2,2,2]) [2,2,2,2,2] = [10] := by decide

-- Constructors expose the exact tree, including every real addition call.
inductive AuditTree where
  | leaf : Nat → AuditTree
  | node : AuditTree → AuditTree → AuditTree
  deriving DecidableEq, Repr
open AuditTree
example : round node [leaf 2, leaf 3, leaf 4, leaf 5, leaf 6] =
  [node (leaf 2) (leaf 5), node (leaf 3) (leaf 6), leaf 4] := by decide
example : stages node 3 [leaf 2, leaf 3, leaf 4, leaf 5, leaf 6] =
  [node (node (node (leaf 2) (leaf 5)) (leaf 4)) (node (leaf 3) (leaf 6))] := by decide
example (t : AuditTree) : round node [t] = [t] := by simp [Bhola.round, Bhola.pairOffset]
example (a b c : AuditTree) : round node [a,b,c] = [node a c,b] := by simp [Bhola.round, Bhola.pairOffset]
example : stages node 3 [leaf 2, leaf 2, leaf 2, leaf 2, leaf 2] =
  [node (node (node (leaf 2) (leaf 2)) (leaf 2)) (node (leaf 2) (leaf 2))] := by decide

-- General nonempty input and least sufficient binary depth.
example (op : α → α → α) (xs : List α) (hne : xs ≠ []) :
    (stages op (depth xs) xs).length = 1 := final_length op xs hne
example (xs : List α) (k : Nat) : depth xs ≤ k ↔ xs.length ≤ 2^k :=
  depth_le_iff xs k

#print axioms Bhola.final_length
#print axioms Bhola.algorithm_exact
#print axioms Bhola.occurrences_preserved
#print axioms Bhola.depth_le_iff
#print axioms Bhola.local_error
#check Bhola.BackwardStable
