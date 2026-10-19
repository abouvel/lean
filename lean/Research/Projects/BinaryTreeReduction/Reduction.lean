import Research.Common.FloatingPoint.Gamma
import Research.Projects.BinaryTreeReduction.Algorithm

/-! # Floating-point binary-tree reduction -/

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- Evaluate a tree using floating-point addition at every internal node. -/
def roundedSum (model : Model) : Tree ℝ → ℝ
  | .leaf value => value
  | .node left right => model.add (roundedSum model left) (roundedSum model right)

/-- `perturbed` has the same shape as `original`, and each perturbed leaf
differs from its original value by at most `bound * |value|`. -/
inductive IsPerturbation (bound : ℝ) : Tree ℝ → Tree ℝ → Prop where
  | leaf (x y : ℝ) (error_le : |y - x| ≤ bound * |x|) :
      IsPerturbation bound (.leaf x) (.leaf y)
  | node {left left' right right' : Tree ℝ}
      (left_ok : IsPerturbation bound left left')
      (right_ok : IsPerturbation bound right right') :
      IsPerturbation bound (.node left right) (.node left' right')

namespace IsPerturbation

/-- A leafwise perturbation remains valid when its nonnegative bound grows. -/
theorem mono {original perturbed : Tree ℝ} {bound nextBound : ℝ}
    (h : IsPerturbation bound original perturbed)
    (hbound : bound ≤ nextBound) :
    IsPerturbation nextBound original perturbed := by
  induction h with
  | leaf x y error_le =>
      apply IsPerturbation.leaf
      exact error_le.trans
        (mul_le_mul_of_nonneg_right hbound (abs_nonneg x))
  | node left_ok right_ok ihLeft ihRight =>
      exact IsPerturbation.node ihLeft ihRight

/-- Compose two leafwise relative perturbations. -/
theorem trans {original middle perturbed : Tree ℝ} {first second : ℝ}
    (hFirst : IsPerturbation first original middle)
    (hSecond : IsPerturbation second middle perturbed)
    (hsecond_nonneg : 0 ≤ second) :
    IsPerturbation (first + second * (1 + first)) original perturbed := by
  induction hFirst generalizing perturbed with
  | leaf x y first_error =>
      cases hSecond with
      | leaf _ z second_error =>
          apply IsPerturbation.leaf
          have hy : |y| ≤ (1 + first) * |x| := by
            calc
              |y| = |(y - x) + x| := by ring_nf
              _ ≤ |y - x| + |x| := abs_add_le _ _
              _ ≤ first * |x| + |x| := add_le_add first_error le_rfl
              _ = (1 + first) * |x| := by ring
          calc
            |z - x| = |(z - y) + (y - x)| := by
              congr 1
              ring
            _ ≤ |z - y| + |y - x| := abs_add_le _ _
            _ ≤ second * |y| + first * |x| :=
              add_le_add second_error first_error
            _ ≤ second * ((1 + first) * |x|) + first * |x| := by
              gcongr
            _ = (first + second * (1 + first)) * |x| := by ring
  | node left_ok right_ok ihLeft ihRight =>
      cases hSecond with
      | node secondLeft secondRight =>
          exact IsPerturbation.node
            (ihLeft secondLeft) (ihRight secondRight)

/-- Multiplying every perturbed leaf by one more relative-error factor
updates the leafwise error bound by `bound + u * (1 + bound)`. -/
theorem scale_one_add {original perturbed : Tree ℝ} {bound nextBound u δ : ℝ}
    (h : IsPerturbation bound original perturbed)
    (hu : 0 ≤ u)
    (hδ : |δ| ≤ u)
    (hnext : bound + u * (1 + bound) ≤ nextBound) :
    IsPerturbation nextBound original (Tree.scale (1 + δ) perturbed) := by
  induction h with
  | leaf x y error_le =>
      apply IsPerturbation.leaf
      have hy : |y| ≤ (1 + bound) * |x| := by
        calc
          |y| = |(y - x) + x| := by ring_nf
          _ ≤ |y - x| + |x| := abs_add_le _ _
          _ ≤ bound * |x| + |x| := add_le_add error_le le_rfl
          _ = (1 + bound) * |x| := by ring
      calc
        |(1 + δ) * y - x| = |(y - x) + δ * y| := by
          congr 1
          ring
        _ ≤ |y - x| + |δ * y| := abs_add_le _ _
        _ = |y - x| + |δ| * |y| := by rw [abs_mul]
        _ ≤ bound * |x| + u * ((1 + bound) * |x|) := by
          gcongr
        _ = (bound + u * (1 + bound)) * |x| := by ring
        _ ≤ nextBound * |x| :=
          mul_le_mul_of_nonneg_right hnext (abs_nonneg x)
  | node left_ok right_ok ihLeft ihRight =>
      exact IsPerturbation.node ihLeft ihRight

end IsPerturbation

/-- A tree whose depth is at most `k` evaluates in floating point as the exact
sum of leaf values perturbed by at most `gamma k u`.

The model's specification incorporates the assumption that every operation
under consideration avoids overflow and underflow.
-/
theorem roundedSum_exists_perturbation_of_depth_le
    (model : Model) (k : ℕ) (tree : Tree ℝ)
    (hdepth : tree.depth ≤ k)
    (hsmall : (k : ℝ) * model.u < 1) :
    ∃ perturbed : Tree ℝ,
      IsPerturbation (gamma k model.u) tree perturbed ∧
      perturbed.exactSum = roundedSum model tree := by
  induction k generalizing tree with
  | zero =>
      cases tree with
      | leaf x =>
          refine ⟨.leaf x, ?_, rfl⟩
          apply IsPerturbation.leaf
          simp
      | node left right =>
          simp [Tree.depth] at hdepth
  | succ k ih =>
      cases tree with
      | leaf x =>
          refine ⟨.leaf x, ?_, rfl⟩
          apply IsPerturbation.leaf
          have hgamma : 0 ≤ gamma (k + 1) model.u :=
            gamma_nonneg (k + 1) model.u model.u_nonneg (by
              norm_num at hsmall ⊢
              exact hsmall)
          simpa using mul_nonneg hgamma (abs_nonneg x)
      | node left right =>
          have hleft_depth : left.depth ≤ k := by
            simp only [Tree.depth] at hdepth
            omega
          have hright_depth : right.depth ≤ k := by
            simp only [Tree.depth] at hdepth
            omega
          have htail_small : (k : ℝ) * model.u < 1 := by
            norm_num at hsmall ⊢
            nlinarith [model.u_nonneg]
          obtain ⟨left', left_ok, left_sum⟩ := ih left hleft_depth htail_small
          obtain ⟨right', right_ok, right_sum⟩ := ih right hright_depth htail_small
          obtain ⟨δ, hδ, hround⟩ :=
            model.round_spec (roundedSum model left + roundedSum model right)
          let scaledLeft := Tree.scale (1 + δ) left'
          let scaledRight := Tree.scale (1 + δ) right'
          refine ⟨Tree.node scaledLeft scaledRight, ?_, ?_⟩
          · apply IsPerturbation.node
            · exact left_ok.scale_one_add
                model.u_nonneg hδ
                (gamma_step k model.u model.u_nonneg (by
                  norm_num at hsmall ⊢
                  exact hsmall))
            · exact right_ok.scale_one_add
                model.u_nonneg hδ
                (gamma_step k model.u model.u_nonneg (by
                  norm_num at hsmall ⊢
                  exact hsmall))
          · simp only [scaledLeft, scaledRight, Tree.exactSum_node,
              Tree.exactSum_scale]
            rw [left_sum, right_sum]
            simp only [roundedSum, Model.add]
            rw [hround]
            ring

/-- Backward-error theorem specialized to the actual depth of a tree. -/
theorem roundedSum_exists_perturbation
    (model : Model) (tree : Tree ℝ)
    (hsmall : (tree.depth : ℝ) * model.u < 1) :
    ∃ perturbed : Tree ℝ,
      IsPerturbation (gamma tree.depth model.u) tree perturbed ∧
      perturbed.exactSum = roundedSum model tree :=
  roundedSum_exists_perturbation_of_depth_le model tree.depth tree le_rfl hsmall

/-- Algorithm 1 specialized backward-error theorem for every nonempty input
list. The constructed tree preserves the inputs, has logarithmic depth, and
its rounded result is the exact sum of leafwise-perturbed inputs. -/
theorem algorithm1_exists_perturbation
    (model : Model) (inputs : List ℝ) (hinputs : inputs ≠ [])
    (hsmall : (Nat.clog 2 inputs.length : ℝ) * model.u < 1) :
    ∃ tree perturbed : Tree ℝ,
      reductionTree inputs = some tree ∧
      tree.leafMultiset = inputs ∧
      tree.depth ≤ Nat.clog 2 inputs.length ∧
      IsPerturbation (gamma (Nat.clog 2 inputs.length) model.u) tree perturbed ∧
      perturbed.exactSum = roundedSum model tree := by
  obtain ⟨tree, htree, hleaves, hdepth⟩ := reductionTree_spec hinputs
  obtain ⟨perturbed, hperturbed, hsum⟩ :=
    roundedSum_exists_perturbation_of_depth_le model
      (Nat.clog 2 inputs.length) tree hdepth hsmall
  exact ⟨tree, perturbed, htree, hleaves, hdepth, hperturbed, hsum⟩

end Research.BinaryTreeReduction
