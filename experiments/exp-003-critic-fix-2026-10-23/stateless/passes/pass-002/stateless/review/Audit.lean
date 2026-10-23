import Research.Submission
open Bhola
#print axioms Bhola.theorem_3_1
#print axioms Bhola.algorithm_exact

def auditValue (values : List Nat) : Tree → Nat
  | .leaf i _ => values[i]!
  | .add _ _ a b => auditValue values a + auditValue values b

def auditInitial (values : List Nat) : List Tree :=
  (List.range values.length).map (fun i => Tree.leaf i 0)

def auditTrace (values : List Nat) : Nat → Nat → List Tree → List (List Nat)
  | 0, _, ts => [ts.map (auditValue values)]
  | fuel+1, l, ts => ts.map (auditValue values) ::
      auditTrace values fuel (l+1) (step values.length l ts)

def traceInput (values : List Nat) :=
  auditTrace values (depth values.length) 0 (auditInitial values)

#eval traceInput [2,3,4,5,6]
#eval traceInput [42]
#eval traceInput [1,2,3]
#eval traceInput [2,2,2,2,2]
#eval ((rounds 5 (depth 5) 0 (auditInitial [2,2,2,2,2])).flatMap Tree.leaves).map Prod.fst

example (l k : Nat) (ts : List Tree) : pair l k ts [] = ts := by cases ts <;> rfl
example (x : ℝ) (δ : Nat → Nat → ℝ) : algorithm [x] δ = x := by
  simp [algorithm, forest, depth, rounds, Tree.eval]

example (xs : List ℝ) (hne : xs ≠ []) (u : ℝ)
    (δ : Nat → Nat → ℝ) (hv : ValidErrors u δ)
    (hd : (depth xs.length : ℝ)*u < 1) :
    ∃ ps : List ((Nat × ℝ) × ℝ),
      (ps.map Prod.fst).Perm (xs.zipIdx.map fun p => (p.2,p.1)) ∧
      algorithm xs δ = (ps.map fun p => p.1.2 + p.2).sum ∧
      ∀ p ∈ ps, |p.2| ≤ gamma u (depth xs.length) * |p.1.2| := by
  obtain ⟨ps, hp, he, hb, _⟩ := theorem_3_1 xs hne u δ hv hd
  exact ⟨ps,hp,he,hb⟩
