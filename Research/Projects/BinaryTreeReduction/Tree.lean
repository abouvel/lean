import Mathlib

/-! # Binary reduction trees -/

namespace Research.BinaryTreeReduction

/-- A binary reduction tree with data stored at its leaves. -/
inductive Tree (α : Type*) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
  deriving Repr

namespace Tree

/-- Number of internal nodes on the longest root-to-leaf path. -/
def depth : Tree α → ℕ
  | leaf _ => 0
  | node left right => 1 + max left.depth right.depth

/-- Number of leaves in a tree. -/
def leafCount : Tree α → ℕ
  | leaf _ => 1
  | node left right => left.leafCount + right.leafCount

/-- Exact real-valued sum represented by a reduction tree. -/
def exactSum : Tree ℝ → ℝ
  | leaf value => value
  | node left right => left.exactSum + right.exactSum

@[simp] theorem depth_leaf (x : α) : (leaf x).depth = 0 := rfl
@[simp] theorem leafCount_leaf (x : α) : (leaf x).leafCount = 1 := rfl

end Tree
end Research.BinaryTreeReduction
