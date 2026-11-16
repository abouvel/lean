# One request through the Lean pipeline

Follow job `cholesky-solve-trial-001-retrieved` from the original LaTeX to the final decision. Steps 1–5 trace the original run. Steps 6–8 trace the semantic replay (`replay-035-12`) on the same Lean candidate.

~~~mermaid
flowchart TD
    S["LaTeX task packet"] --> P["Planner"]
    M["Approved artifact snapshot"] -.-> P
    M -.-> F["Formalizer"]
    M -.-> B["Prover"]
    P -->|"proof plan"| F
    F -->|"Lean statement and definitions"| B
    B -->|"completed Lean proof"| V["Lean verification · pass"]
    V --> C["Direct critic · pass"]
    V --> T["Blind translator · replay"]
    T -->|"plain-language statement"| J["Round-trip judge · pass"]
    S -.->|"original source"| J
    C --> A["Accepted in replay"]
    J --> A
~~~

## 1. Submit a paper theorem as the request

The request selects `theorem:cholesky_solve` in `main.tex`. The task packet gives each proof agent `PROMPT.txt` with the task instructions, `source.txt` with the selected theorem and its context, and `paper.tex` with the full manuscript and mathematical proof. The prompt permits proving earlier paper results as helpers. The Lean workspace starts with `import Mathlib` in `Research/Submission.lean`.

~~~latex
$\hat{\vect{x}}$ satisfies
\begin{align}
    (\mat{a}+\Delta\mat{a})\hat{\vect{x}}=\vect{b},
\end{align}
~~~

The source assumes a symmetric positive-definite matrix $A$, successful Cholesky factorization, no overflow or underflow, and $(n+1)u<1$. The computed factor $R$ comes from $A$, forward substitution uses $R^\top$ and the original right-hand side $b$, and backward substitution produces $x$. The required output is a proof that some $\Delta A$ satisfies $(A+\Delta A)x=b$ and the entrywise chain

$$
|\Delta A_{ij}| \le
(\gamma_{n+1}+2\gamma_n+\gamma_n^2) B_{ij} \le
(3\gamma_{n+1}+\gamma_n^2) B_{ij},
\qquad B_{ij}=\sum_k |R_{ki}|\,|R_{kj}|,\quad
\gamma_m=\frac{mu}{1-mu}.
$$

[Original manuscript][paper] · [Task prompt][prompt] · [Selected source packet][source] · [Initial Lean file][initial]

## 2. Retrieve an artifact and hand off a plan

The three proof agents run in separate sessions. This job's `retrieved` condition gives those roles read-only access to the approved snapshot in `/memory`. The planner starts with the task packet and snapshot and searches for `cholesky_solve` and related Cholesky and triangular-solve terms. It opens `pilot-general-lean-001` and records what it took from that note in `retrieval.json`.

> Plan gamma arithmetic around explicit positivity of denominators before clearing rational inequalities; use abs_add_le for scalar absolute-value estimates underlying componentwise bounds.

The planner writes `plan.json` with a strategy and named obligations such as `operational_construction` and `total_perturbation`. The central plan is to prove the rounded factorization and triangular-solve bounds, then combine the factorization residual $E_f$ and the two solve perturbations $L$ and $U$ into $\Delta A=E_f+R^\top U+LR+LU$. The four summands account for the four contributions in $\gamma_{n+1}+2\gamma_n+\gamma_n^2$. The harness checks the handoff schema and passes the plan to the formalizer.

[Frozen note][memory] · [Planner retrieval log][planner-memory] · [Planner output][plan] · [Handoff code][handoff]

## 3. Formalize the construction and theorem

The formalizer gets the original task packet, `plan.json`, and the Lean workspace. It builds the rounded operations and an operational relation for each of the three stages. `SolveRun` then ties the stage inputs and outputs together.

~~~lean
structure SolveRun {n : ℕ} (u : ℝ) (rnd : ℝ → ℝ)
    (A : Mat n) (b : Vec n) (R : Mat n) (y x : Vec n) : Prop where
  factorization : CholeskyRun u rnd A R
  forward : ForwardRun u rnd R.transpose b y
  backward : BackwardRun u rnd R y x
~~~

The two substitution relations constrain each row by the rounded update using earlier indices for the forward solve and later indices for the backward solve. The final statement takes `SolveRun u rnd A b R y x` as a hypothesis. This certifies that the given $R,y,x$ satisfy the recurrences. The conclusion refers to exactly those values.

~~~lean
    (hrun : SolveRun u rnd A b R y x) :
    ∃ ΔA : Mat n,
      (A + ΔA).mulVec x = b ∧
~~~

The full theorem states both bounds after this equation. The formalizer records one target (`CholeskySolve.cholesky_solve`), 20 construction names, and a source mapping in `statement.json`. The harness compiles and records the elaborated declarations before handing the workspace to the prover. The intermediate audit found `sorryAx`, which is permitted for temporary proof scaffolding at this stage.

The manuscript displays the relative-error model for the four basic operations and uses a rounded square root in the diagonal update. The formalizer makes that step explicit with `sqrt_valid`. For the exact square-root result $t$, it requires a $\delta$ with $|\delta|\le u$ and $\operatorname{rnd}(t)=t(1+\delta)$. The proof derives the matrix error bound from these local operation conditions and a successful run.

[Run relations][construction] · [Lean statement][proof] · [Statement handoff][statement] · [Intermediate audit][skeleton-audit]

## 4. Prove the stated theorem and run the formal gate

The prover receives the source packet, `plan.json`, `statement.json`, and the formalizer's workspace. It fills the proof placeholder and adds supporting lemmas. The formalizer had opened the memory note and recorded zero decisions influenced by it. The prover reported using positive denominators in the $\gamma$ inequalities and `abs_add_le` in the entrywise estimates. The completed proof contains those proof steps.

The proof derives $(R^\top+L)y=b$ from the forward run and $(R+U)x=y$ from the backward run. After constructing the perturbation, it rewrites $A+\Delta A$ as $(R^\top+L)(R+U)$ and applies the two equations in order. This is where the proof gets back to the original $b$.

~~~lean
  refine ⟨solvePerturbation A R L U, ?_, ?_, ?_⟩
  · have he : A + solvePerturbation A R L U = (R.transpose + L) * (R + U) := by
      unfold solvePerturbation factorResidual
      noncomm_ring
    rw [he, ← Matrix.mulVec_mulVec, hUsolve, hLsolve]
~~~

The harness runs `bash pipeline/verify.sh` on the completed candidate. The build and scans pass. A separate elaboration audit checks protected prerequisites and transitive axioms and compares the formalizer's declaration types, kinds, and definition bodies with the completed candidate. The saved result has `formal_gate_passed: true` and empty lists for changed declarations and unapproved axioms.

[Formalizer retrieval log][formalizer-memory] · [Prover retrieval log][prover-memory] · [Proof excerpt][proof-step] · [Verification log][lean-log] · [Final audit][audit]

## 5. Review the Lean code directly

After the formal gate, the direct critic receives the read-only Lean candidate, the original source, the verification evidence, and a fixed rubric. The rubric asks about the final theorem, the actual construction, both bounds, input linkage, and assumptions. The critic can inspect the Lean declaration and proof directly. Its `original-input-link` evidence points to `SolveRun` and the final rewrite as the places to check that $A,b,R,y,x$ are the same values through the run and theorem. It records `pass` for all five requirements.

[Direct critic instructions][critic-spec] · [Requirement catalog][rubric] · [Original direct critic report][direct]

## 6. Build the blind translator's input

In the original run, the controller tried to assemble the translator bundle after the direct critic finished. It stopped with `Construction is absent or is not a definition: CholeskySolve.CholeskyRun`. Lean had elaborated `CholeskyRun` as a structure, which is an inductive declaration. The exporter at the time accepted only definitions, so the original job ended with `infrastructure_error` before any translation or round-trip judgment.

The replay exporter accepts inductive types and includes their constructors. Prep checks the archived candidate fingerprint and source hashes and checks that the critic used the same source and rubric. It then reuses the Lean verification and direct critic report and launches the two semantic agents. The translator receives `formal-context.json` with one target, 20 named constructions, and 30 project declarations including dependencies. The bundle contains elaborated types, definition bodies, and environment metadata. The translator's isolated spec omits the LaTeX task, source comments, proof terms, prior verdicts, and research memory.

[Original result][original-result] · [Replay preparation code][replay-code] · [Translator input][bundle] · [Translator instructions][translator-spec]

## 7. Translate the candidate, then compare it with the source

**Translator output.** `translation.json` renders the target and gives a mathematical description of each construction. For `SolveRun`, it identifies the constructor's three proof fields as `CholeskyRun(u,rnd,A,R)`, `ForwardRun(u,rnd,R^T,b,y)`, and `BackwardRun(u,rnd,R,y,x)`. The conclusion in its target rendering is quoted below.

> There exists a real n by n matrix DeltaA such that (A+DeltaA)x=b, and such that for every i,j in I_n, |DeltaA_{ij}|<=C B_{ij}, and for every i,j in I_n, C B_{ij}<=D B_{ij}.

The report expands $C$, $D$, and $B$ to the coefficients and matrix entries in Step 1. Before invoking the judge, the harness checks the candidate hash and that the translation covers every requested target and construction exactly once.

**Judge input and output.** The judge receives the validated translation, original `source.txt`, and requirement contract in its own isolated workspace. It has no candidate Lean code or direct critic verdict. It sees that the source calls for the solution produced by the three stages and that the translated `SolveRun` binds the output of each stage to the next. It records this evidence:

> The same A,b occur in the perturbed equation; the same computed R occurs in its bound, and the same computed x occurs in its equation.

The judge also checks that the selected Lean theorem already states the equation and both inequalities, and that they hold under the source hypotheses. For this case it sets both `lean_implies_source` and `source_implies_lean` to `true`, marks `relation: faithful`, and sets both `delivery_complete` and `construction_complete` to `true` with `missing_formal_steps: []`. These are the judge's semantic findings. Lean checks the proof of the formal statement in Step 4.

[Translation][translation] · [Judge instructions][judge-spec] · [Judge contract][judge-contract] · [Judge report][judgment]

## 8. Record the final decision

The controller validates the report schema, required evidence fields, candidate hash, and consistency of the semantic flags. A round-trip pass requires a complete translation, both completeness flags, entailment from the translated Lean claim to the source, no added assumptions or missing formal steps, and a consistent relation label. In the calibration router, two reviewer passes yield `accepted`, two failures yield `critic_failed`, and disagreement or uncertainty yields `needs_human`.

The replay's `result.json` records `outcome: accepted`. Inside `record.passes[0]`, `verification` and `direct_report` are the saved original checks, `roundtrip` is the fresh judge report, and `roles` contains the fresh translator and judge metrics. The formal audit, translation, and judgment all carry the same candidate hash. Independent expert adjudication remains pending in the replay report.

[Validation and routing code][decision-code] · [Final result][result] · [Replay report](REPORT.md)

[paper]: ../exp-033-block-jacobi-proof-packets-2026-11-06/original/main.tex#L550
[prompt]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/inputs/PROMPT.txt
[source]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/inputs/source.txt
[initial]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/preflight/workspace/Research/Submission.lean
[memory]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/memory/general-lean.md
[planner-memory]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/retrieved/passes/pass-001/retrieved/roles/planner/retrieval.json
[formalizer-memory]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/retrieved/passes/pass-001/retrieved/roles/formalizer/retrieval.json
[prover-memory]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/retrieved/passes/pass-001/retrieved/roles/prover/retrieval.json
[plan]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/retrieved/passes/pass-001/retrieved/roles/planner/plan.json#L3
[handoff]: ../../pipeline/roles.py#L172
[statement]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/retrieved/passes/pass-001/retrieved/roles/formalizer/statement.json
[skeleton-audit]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/retrieved/passes/pass-001/retrieved/formal-audit/formalizer/audit.json
[construction]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/retrieved/passes/pass-001/retrieved/workspace/Research/Submission.lean#L83-L116
[proof]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/retrieved/passes/pass-001/retrieved/workspace/Research/Submission.lean#L642
[proof-step]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/retrieved/passes/pass-001/retrieved/workspace/Research/Submission.lean#L680-L684
[lean-log]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/retrieved/passes/pass-001/retrieved/evaluation/verification.log
[audit]: replay-035-12/prior-verification.json
[critic-spec]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/retrieved/passes/pass-001/retrieved/reviewer-spec/REVIEWER.txt
[rubric]: replay-035-12/evaluator/requirements.json
[original-result]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/result.json#L88
[direct]: ../exp-034-block-jacobi-roundtrip-2026-11-06/runs/cholesky-solve-trial-001-retrieved/retrieved/passes/pass-001/retrieved/review/review.json#L31
[replay-code]: ../../pipeline/replay_construction_reviews.py#L32
[bundle]: replay-035-12/stateless/role-spec/translator/formal-context.json
[translator-spec]: replay-035-12/stateless/role-spec/translator/ROLE.txt
[translation]: replay-035-12/stateless/roles/translator/translation.json#L5
[judge-spec]: replay-035-12/stateless/role-spec/judge/ROLE.txt
[judge-contract]: replay-035-12/stateless/role-spec/judge/contract.json
[judgment]: replay-035-12/stateless/roles/judge/roundtrip.json#L41
[decision-code]: ../../pipeline/roundtrip.py#L104-L169
[result]: replay-035-12/result.json#L4
