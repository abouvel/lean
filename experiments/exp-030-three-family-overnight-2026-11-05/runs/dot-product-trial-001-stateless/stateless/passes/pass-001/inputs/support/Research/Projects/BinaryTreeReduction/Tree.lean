import Mathlib

/-! # Binary reduction trees -/

namespace Research.BinaryTreeReduction

/-- A binary reduction tree with data stored at its leaves. -/
inductive Tree (α : Type*) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
  deriving Repr

namespace Tree

/-- Apply a function to every leaf while preserving the reduction shape. -/
def map (f : α → β) : Tree α → Tree β
  | leaf value => leaf (f value)
  | node left right => node (map f left) (map f right)

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

/-- Multiply every leaf in a tree by the same scalar. -/
def scale (c : ℝ) : Tree ℝ → Tree ℝ
  | leaf value => leaf (c * value)
  | node left right => node (scale c left) (scale c right)

@[simp] theorem depth_leaf (x : α) : (leaf x).depth = 0 := rfl
@[simp] theorem leafCount_leaf (x : α) : (leaf x).leafCount = 1 := rfl

@[simp] theorem depth_map (f : α → β) (tree : Tree α) :
    (tree.map f).depth = tree.depth := by
  induction tree with
  | leaf value => rfl
  | node left right ihLeft ihRight => simp [map, depth, ihLeft, ihRight]

@[simp] theorem exactSum_leaf (x : ℝ) : (leaf x).exactSum = x := rfl

@[simp] theorem exactSum_node (left right : Tree ℝ) :
    (node left right).exactSum = left.exactSum + right.exactSum := rfl

@[simp] theorem exactSum_scale (c : ℝ) (tree : Tree ℝ) :
    (scale c tree).exactSum = c * tree.exactSum := by
  induction tree with
  | leaf value => rfl
  | node left right ihLeft ihRight =>
      simp only [scale, exactSum_node, ihLeft, ihRight]
      ring

end Tree
end Research.BinaryTreeReduction
