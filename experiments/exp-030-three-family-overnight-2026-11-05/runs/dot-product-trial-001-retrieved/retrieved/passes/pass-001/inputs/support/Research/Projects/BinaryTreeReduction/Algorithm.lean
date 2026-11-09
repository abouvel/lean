import Research.Projects.BinaryTreeReduction.Tree

/-! # Algorithm 1: offset-paired parallel binary-tree reduction -/

namespace Research.BinaryTreeReduction

/-- Pair corresponding trees from two halves. If the left half has an
unmatched final tree, carry it forward unchanged. -/
def combineHalves : List (Tree α) → List (Tree α) → List (Tree α)
  | left, [] => left
  | [], right => right
  | left :: lefts, right :: rights =>
      .node left right :: combineHalves lefts rights

/-- One level of Algorithm 1. The split point is `⌈n/2⌉ = (n+1)/2`, so
the first active partial sum is paired with the first partial sum in the
second half. -/
def reductionRound (forest : List (Tree α)) : List (Tree α) :=
  let half := (forest.length + 1) / 2
  combineHalves (forest.take half) (forest.drop half)

/-- Record the initial forest and then `rounds` successive reduction levels. -/
def reductionLevelsFromForest : ℕ → List (Tree α) → List (List (Tree α))
  | 0, forest => [forest]
  | rounds + 1, forest =>
      forest :: reductionLevelsFromForest rounds (reductionRound forest)

/-- Apply exactly `rounds` levels of Algorithm 1. -/
def runRounds : ℕ → List (Tree α) → List (Tree α)
  | 0, forest => forest
  | rounds + 1, forest => runRounds rounds (reductionRound forest)

/-- Algorithm 1 levels for a list of inputs. -/
def reductionLevels (inputs : List α) : List (List (Tree α)) :=
  reductionLevelsFromForest (Nat.clog 2 inputs.length) (inputs.map .leaf)

/-- Read the exact partial sums at every recorded level. -/
def exactLevelValues (levels : List (List (Tree ℝ))) : List (List ℝ) :=
  levels.map fun forest => forest.map Tree.exactSum

/-- The numerical length recurrence induced by one reduction round. -/
def roundLengthAfter : ℕ → ℕ → ℕ
  | 0, n => n
  | rounds + 1, n => roundLengthAfter rounds ((n + 1) / 2)

/-- All leaves in a tree, with multiplicity but without imposing an order. -/
def Tree.leafMultiset : Tree α → Multiset α
  | .leaf value => {value}
  | .node left right => left.leafMultiset + right.leafMultiset

theorem Tree.exactSum_eq_leafMultiset_sum (tree : Tree ℝ) :
    tree.exactSum = tree.leafMultiset.sum := by
  induction tree with
  | leaf value => simp [Tree.exactSum, Tree.leafMultiset]
  | node left right ihLeft ihRight =>
      simp [Tree.exactSum, Tree.leafMultiset, ihLeft, ihRight]

/-- All leaves in a forest, counted with multiplicity. -/
def forestLeafMultiset (forest : List (Tree α)) : Multiset α :=
  (forest.map Tree.leafMultiset).sum

@[simp] theorem combineHalves_length (left right : List (Tree α)) :
    (combineHalves left right).length = max left.length right.length := by
  induction left generalizing right with
  | nil => cases right <;> simp [combineHalves]
  | cons tree trees ih =>
      cases right with
      | nil => simp [combineHalves]
      | cons other others => simp [combineHalves, ih, Nat.succ_max_succ]

theorem reductionRound_length (forest : List (Tree α)) :
    (reductionRound forest).length = (forest.length + 1) / 2 := by
  simp only [reductionRound, combineHalves_length, List.length_take,
    List.length_drop]
  omega

theorem reductionRound_nonempty {forest : List (Tree α)}
    (h : forest ≠ []) : reductionRound forest ≠ [] := by
  cases forest with
  | nil => exact (h rfl).elim
  | cons tree trees =>
      intro hempty
      have hlength := congrArg List.length hempty
      rw [reductionRound_length] at hlength
      simp at hlength
      omega

theorem reductionRound_shorter {forest : List (Tree α)}
    (h : 2 ≤ forest.length) :
    (reductionRound forest).length < forest.length := by
  rw [reductionRound_length]
  omega

theorem runRounds_length (rounds : ℕ) (forest : List (Tree α)) :
    (runRounds rounds forest).length = roundLengthAfter rounds forest.length := by
  induction rounds generalizing forest with
  | zero => rfl
  | succ rounds ih =>
      simp only [runRounds, roundLengthAfter, ih, reductionRound_length]

/-- Repeated ceiling-halving of a positive number reaches one after its
base-two ceiling logarithm number of rounds. -/
theorem roundLengthAfter_clog_two (n : ℕ) (hn : 0 < n) :
    roundLengthAfter (Nat.clog 2 n) n = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn_one : n ≤ 1
      · have hn_eq : n = 1 := by omega
        subst n
        simp [roundLengthAfter]
      · have hn_two : 2 ≤ n := by omega
        let next := (n + 1) / 2
        have hnext_pos : 0 < next := by
          dsimp [next]
          omega
        have hnext_lt : next < n := by
          dsimp [next]
          omega
        have hclog : Nat.clog 2 n = Nat.clog 2 next + 1 := by
          rw [Nat.clog_of_two_le (by decide) hn_two]
          congr 2
        rw [hclog]
        simp only [roundLengthAfter]
        exact ih next hnext_lt hnext_pos

/-- The active forest after the number of rounds prescribed by Algorithm 1. -/
def finalForest (inputs : List α) : List (Tree α) :=
  runRounds (Nat.clog 2 inputs.length) (inputs.map .leaf)

theorem finalForest_length {inputs : List α} (h : inputs ≠ []) :
    (finalForest inputs).length = 1 := by
  rw [finalForest, runRounds_length, List.length_map]
  apply roundLengthAfter_clog_two
  cases inputs with
  | nil => exact (h rfl).elim
  | cons value values => simp

/-- Extract the unique final tree. Empty input returns `none`. -/
def reductionTree (inputs : List α) : Option (Tree α) :=
  match finalForest inputs with
  | [tree] => some tree
  | _ => none

@[simp] theorem forestLeafMultiset_append
    (left right : List (Tree α)) :
    forestLeafMultiset (left ++ right) =
      forestLeafMultiset left + forestLeafMultiset right := by
  simp [forestLeafMultiset]

theorem forestLeafMultiset_combineHalves
    (left right : List (Tree α)) :
    forestLeafMultiset (combineHalves left right) =
      forestLeafMultiset left + forestLeafMultiset right := by
  induction left generalizing right with
  | nil => cases right <;> simp [combineHalves, forestLeafMultiset]
  | cons tree trees ih =>
      cases right with
      | nil => simp [combineHalves, forestLeafMultiset]
      | cons other others =>
          simp only [combineHalves, forestLeafMultiset, List.map_cons,
            List.sum_cons, Tree.leafMultiset]
          have hih := ih others
          unfold forestLeafMultiset at hih
          rw [hih]
          simp only [add_assoc, add_comm, add_left_comm]

/-- A reduction round neither loses nor duplicates an input leaf. -/
theorem forestLeafMultiset_reductionRound (forest : List (Tree α)) :
    forestLeafMultiset (reductionRound forest) = forestLeafMultiset forest := by
  rw [reductionRound]
  rw [forestLeafMultiset_combineHalves]
  rw [← forestLeafMultiset_append]
  rw [List.take_append_drop]

theorem forestLeafMultiset_runRounds (rounds : ℕ)
    (forest : List (Tree α)) :
    forestLeafMultiset (runRounds rounds forest) =
      forestLeafMultiset forest := by
  induction rounds generalizing forest with
  | zero => rfl
  | succ rounds ih =>
      simp only [runRounds]
      rw [ih, forestLeafMultiset_reductionRound]

/-- Every input appears once in the initial leaf forest. -/
@[simp] theorem forestLeafMultiset_map_leaf (inputs : List α) :
    forestLeafMultiset (inputs.map Tree.leaf) = inputs := by
  induction inputs with
  | nil => simp [forestLeafMultiset]
  | cons value values ih =>
      change {value} + forestLeafMultiset (values.map Tree.leaf) =
        (value :: values : Multiset α)
      rw [ih]
      rfl

/-- Every tree in a forest has depth at most `bound`. -/
def ForestDepthLE (bound : ℕ) (forest : List (Tree α)) : Prop :=
  ∀ tree ∈ forest, tree.depth ≤ bound

theorem combineHalves_depth_le {left right : List (Tree α)} {bound : ℕ}
    (hleft : ForestDepthLE bound left)
    (hright : ForestDepthLE bound right) :
    ForestDepthLE (bound + 1) (combineHalves left right) := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => simp [ForestDepthLE, combineHalves]
      | cons tree trees =>
          intro candidate hcandidate
          exact (hright candidate (by simpa [combineHalves] using hcandidate)).trans
            (Nat.le_succ bound)
  | cons tree trees ih =>
      cases right with
      | nil =>
          intro candidate hcandidate
          exact (hleft candidate (by simpa [combineHalves] using hcandidate)).trans
            (Nat.le_succ bound)
      | cons other others =>
          have htree : tree.depth ≤ bound := hleft tree (by simp)
          have hother : other.depth ≤ bound := hright other (by simp)
          have htrees : ForestDepthLE bound trees := by
            intro candidate hcandidate
            exact hleft candidate (by simp [hcandidate])
          have hothers : ForestDepthLE bound others := by
            intro candidate hcandidate
            exact hright candidate (by simp [hcandidate])
          intro candidate hcandidate
          simp only [combineHalves, List.mem_cons] at hcandidate
          rcases hcandidate with rfl | hcandidate
          · simp only [Tree.depth]
            omega
          · exact ih htrees hothers candidate hcandidate

theorem reductionRound_depth_le {forest : List (Tree α)} {bound : ℕ}
    (hdepth : ForestDepthLE bound forest) :
    ForestDepthLE (bound + 1) (reductionRound forest) := by
  apply combineHalves_depth_le
  · intro tree htree
    exact hdepth tree (List.mem_of_mem_take htree)
  · intro tree htree
    exact hdepth tree (List.mem_of_mem_drop htree)

theorem runRounds_depth_le {forest : List (Tree α)} {bound : ℕ}
    (hdepth : ForestDepthLE bound forest) (rounds : ℕ) :
    ForestDepthLE (bound + rounds) (runRounds rounds forest) := by
  induction rounds generalizing forest bound with
  | zero => simpa [runRounds] using hdepth
  | succ rounds ih =>
      simp only [runRounds]
      have hround := reductionRound_depth_le hdepth
      have hresult := ih hround
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hresult

theorem finalForest_preserves_inputs (inputs : List α) :
    forestLeafMultiset (finalForest inputs) = inputs := by
  simp [finalForest, forestLeafMultiset_runRounds]

theorem finalForest_depth_le (inputs : List α) :
    ForestDepthLE (Nat.clog 2 inputs.length) (finalForest inputs) := by
  unfold finalForest
  have hinitial : ForestDepthLE 0 (inputs.map Tree.leaf) := by
    intro tree htree
    simp only [List.mem_map] at htree
    obtain ⟨value, _, rfl⟩ := htree
    simp
  simpa using runRounds_depth_le hinitial (Nat.clog 2 inputs.length)

/-- Algorithm 1 returns one tree for every nonempty input. That tree contains
exactly the input multiset and has depth at most `Nat.clog 2 inputs.length`. -/
theorem reductionTree_spec {inputs : List α} (hinputs : inputs ≠ []) :
    ∃ tree : Tree α,
      reductionTree inputs = some tree ∧
      tree.leafMultiset = inputs ∧
      tree.depth ≤ Nat.clog 2 inputs.length := by
  have hlength := finalForest_length hinputs
  have hpreserve := finalForest_preserves_inputs inputs
  have hdepth := finalForest_depth_le inputs
  cases hforest : finalForest inputs with
  | nil => simp [hforest] at hlength
  | cons tree trees =>
      cases trees with
      | nil =>
          refine ⟨tree, ?_, ?_, ?_⟩
          · simp [reductionTree, hforest]
          · simpa [hforest, forestLeafMultiset] using hpreserve
          · exact hdepth tree (by simp [hforest])
      | cons other others => simp [hforest] at hlength

/-- For real inputs, the tree returned by Algorithm 1 has exactly the same
real-valued sum as the input list. -/
theorem reductionTree_exactSum {inputs : List ℝ} {tree : Tree ℝ}
    (htree : reductionTree inputs = some tree) :
    tree.exactSum = inputs.sum := by
  by_cases hinputs : inputs = []
  · subst inputs
    simp [reductionTree, finalForest, runRounds] at htree
  · obtain ⟨result, hresult, hleaves, _⟩ := reductionTree_spec hinputs
    rw [hresult] at htree
    cases htree
    rw [Tree.exactSum_eq_leafMultiset_sum, hleaves]
    simp

end Research.BinaryTreeReduction
