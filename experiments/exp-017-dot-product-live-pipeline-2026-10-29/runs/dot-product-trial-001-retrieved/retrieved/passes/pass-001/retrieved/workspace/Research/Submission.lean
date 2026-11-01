import Research.Projects.BinaryTreeReduction.Reduction

namespace Research.BinaryTreeReduction

open Research.FloatingPoint

/-- Exact componentwise products, preserving the input reduction shape. -/
def exactProductTree (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map fun p => p.1 * p.2

/-- Each leaf multiplication is rounded once before any additions. -/
def roundedProductTree (model : Model) (tree : Tree (ℝ × ℝ)) : Tree ℝ :=
  tree.map fun p => model.mul p.1 p.2

/-- Rounded componentwise multiplication followed by rounded tree addition. -/
def roundedDotProduct (model : Model) (tree : Tree (ℝ × ℝ)) : ℝ :=
  roundedSum model (roundedProductTree model tree)

lemma u_le_gamma_succ (model : Model) (k : ℕ)
    (hsmall : ((k + 1 : ℕ) : ℝ) * model.u < 1) :
    model.u ≤ gamma (k + 1) model.u := by
  have htail : (k : ℝ) * model.u < 1 := by
    push_cast at hsmall
    nlinarith [model.u_nonneg]
  have hg := gamma_nonneg k model.u model.u_nonneg htail
  have hs := gamma_step k model.u model.u_nonneg hsmall
  nlinarith [mul_nonneg model.u_nonneg hg]

/-- A budget of `k` additions and one multiplication per leaf suffices. -/
theorem roundedDotProduct_exists_perturbation_of_depth_le
    (model : Model) (k : ℕ) (tree : Tree (ℝ × ℝ))
    (hdepth : tree.depth ≤ k)
    (hsmall : ((k + 1 : ℕ) : ℝ) * model.u < 1) :
    ∃ perturbed : Tree ℝ,
      IsPerturbation (gamma (k + 1) model.u) (exactProductTree tree) perturbed ∧
      perturbed.exactSum = roundedDotProduct model tree := by
  induction k generalizing tree with
  | zero =>
      cases tree with
      | leaf p =>
          obtain ⟨δ, hδ, hr⟩ := model.round_spec (p.1 * p.2)
          refine ⟨.leaf (model.mul p.1 p.2), ?_, rfl⟩
          apply IsPerturbation.leaf
          change |model.round (p.1 * p.2) - p.1 * p.2| ≤ _
          rw [hr]
          calc
            |p.1 * p.2 * (1 + δ) - p.1 * p.2| = |δ| * |p.1 * p.2| := by
              rw [← abs_mul]; congr 1; ring
            _ ≤ gamma (0 + 1) model.u * |p.1 * p.2| :=
              mul_le_mul_of_nonneg_right (hδ.trans (u_le_gamma_succ model 0 hsmall))
                (abs_nonneg _)
      | node left right => simp [Tree.depth] at hdepth
  | succ k ih =>
      cases tree with
      | leaf p =>
          obtain ⟨δ, hδ, hr⟩ := model.round_spec (p.1 * p.2)
          refine ⟨.leaf (model.mul p.1 p.2), ?_, rfl⟩
          apply IsPerturbation.leaf
          change |model.round (p.1 * p.2) - p.1 * p.2| ≤ _
          rw [hr]
          calc
            |p.1 * p.2 * (1 + δ) - p.1 * p.2| = |δ| * |p.1 * p.2| := by
              rw [← abs_mul]; congr 1; ring
            _ ≤ gamma (k + 1 + 1) model.u * |p.1 * p.2| :=
              mul_le_mul_of_nonneg_right
                (hδ.trans (u_le_gamma_succ model (k + 1) hsmall)) (abs_nonneg _)
      | node left right =>
          have hl : left.depth ≤ k := by simp only [Tree.depth] at hdepth; omega
          have hr : right.depth ≤ k := by simp only [Tree.depth] at hdepth; omega
          have ht : ((k + 1 : ℕ) : ℝ) * model.u < 1 := by
            push_cast at hsmall ⊢
            nlinarith [model.u_nonneg]
          obtain ⟨left', hleft, hsleft⟩ := ih left hl ht
          obtain ⟨right', hright, hsright⟩ := ih right hr ht
          obtain ⟨δ, hδ, hround⟩ := model.round_spec
            (roundedDotProduct model left + roundedDotProduct model right)
          refine ⟨.node (Tree.scale (1 + δ) left') (Tree.scale (1 + δ) right'), ?_, ?_⟩
          · exact IsPerturbation.node
              (hleft.scale_one_add model.u_nonneg hδ
                (gamma_step (k + 1) model.u model.u_nonneg hsmall))
              (hright.scale_one_add model.u_nonneg hδ
                (gamma_step (k + 1) model.u model.u_nonneg hsmall))
          · simp only [Tree.exactSum_node, Tree.exactSum_scale, hsleft, hsright]
            change _ = model.round
              (roundedDotProduct model left + roundedDotProduct model right)
            rw [hround]
            ring

/-- Componentwise backward stability for every model and every pair tree:
one multiplication and at most `depth` additions affect each exact product. -/
theorem roundedDotProduct_exists_perturbation
    (model : Model) (tree : Tree (ℝ × ℝ))
    (hsmall : ((tree.depth + 1 : ℕ) : ℝ) * model.u < 1) :
    ∃ perturbed : Tree ℝ,
      IsPerturbation (gamma (tree.depth + 1) model.u)
        (exactProductTree tree) perturbed ∧
      perturbed.exactSum = roundedDotProduct model tree := by
  exact roundedDotProduct_exists_perturbation_of_depth_le
    model tree.depth tree le_rfl hsmall

end Research.BinaryTreeReduction
