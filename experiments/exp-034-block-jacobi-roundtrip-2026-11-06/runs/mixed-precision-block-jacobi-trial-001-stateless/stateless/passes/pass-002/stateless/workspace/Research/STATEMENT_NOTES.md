# Statement handoff

Authoritative source: `/spec/source.txt`, selected theorem
`theorem:mixed_precision_update_form_block_jacobi_in_floating_point_arithmetic`;
its proof and algorithmic context occur in `/spec/paper.tex`, lines 703–1270.
`/spec/plan.json` was consulted only as a fallible proof handoff.

## Feedback and statement revision record

Read `/spec/feedback.json` (previous pass 1). It reports a successful build but
failure of proof verification because the final one-step estimate contains
`sorry`; its corrections list is empty. **No mathematical statement revisions
were made in this formalizer pass.** The existing operation-level constructions
and full theorem signature were audited against the selected source and
retained. This pass adds this explanatory record and the machine-readable
statement manifest. The single temporary proof placeholder remains for the
next, proving role, as explicitly permitted by this role's instructions.
Compilation of a skeleton is not a claim that the theorem has been proved.

## Source interpretation and explicit assumptions

* `Fin n ≃ Fin B × Fin T` specifies the exact block partition, permitting a
  coordinate permutation. `hT` and `hS` specify positive block and tile sizes;
  `hdiv` specifies `S ∣ n`. No positivity restriction is imposed on `n` or `B`.
* `blocks` are the original symmetric positive definite blocks, expressed by
  `Matrix.PosDef` over the reals. `D = blockDiagonal layout blocks` and
  `A = D + N`. Its inverse in all constants is Mathlib's genuine matrix inverse;
  invertibility is derived from positive definiteness, not assumed separately.
* `x` is any exact solution of `A.mulVec x = b`; the initial iterate is arbitrary.
* `0 ≤ us < uc`, `(S + n/S - 1) * us < 1`, and `(T+1) * uc < 1`
  express valid unit roundoffs and positive relevant gamma denominators. The
  latter also ensures `T * uc < 1`. The source's no overflow/underflow
  condition is encoded by validity of the real relative-error model at every
  arithmetic operation, through `Execution.Admissible`.
* Every scalar operation has an addressed local relative error. Errors are
  universally quantified deterministic tapes; no probabilistic independence
  assumption is imposed. Subtapes separate operation addresses. Products and
  sums are evaluated sequentially within tiles and then across tile results.
* Cholesky is the column-oriented upper-triangular recurrence, initialized at
  zero. Empty inner products omit the subtraction from zero. Square roots
  obey the same relative-error bound (the usual rounded-square-root model
  used for Cholesky analysis). A nonpositive square-root argument or zero
  off-diagonal divisor produces `none`. `hsuccess` requires the factors to
  exist, corresponding to the source's computed-factor premise and the
  explicit success condition in its earlier Cholesky-solve theorem. It does
  not assume any backward-error estimate.
* Factorizations are performed once and reused. Forward and backward
  substitutions have fresh tapes at each step. The residual is converted to
  correction precision with relative error at most `uc`, as in the paper's
  `Delta rhat` term; exact conversion is included by choosing zero errors.
  Residual subtraction and solution addition use precision `us`.
* `computedFactors`, `iterates`, and `error` are actual constructed outputs of
  these kernels. Neither an algorithmic error bound nor the desired recurrence
  is a hypothesis of the final theorem.
* `vectorInfNorm` is maximum absolute entry; `matrixInfNorm` is maximum
  absolute row sum, both zero on empty index types. The default entrywise
  Mathlib matrix norm is not used. `gamma`, `c₁`, `c₂`, `gain`, `eta`, `q`, `p`,
  `alpha`, and `beta` reproduce the displayed formulas exactly.
* `eta < 1` is assumed for the one-step inequality. Only the geometric and
  limsup conclusions additionally require `alpha < 1`; no restriction `q < 1`
  is added. The limsup is the real `Filter.limsup` at `Filter.atTop`.

## Remaining proof obligation

The target contains one temporary `sorry`, in `hstep`. The next role must prove
the one-step estimate from the concrete tiled matvec, Cholesky, substitution,
conversion, and update kernels. In particular, the tiled-matvec estimate and
Cholesky/triangular-solve backward-error bridges cannot be assumed as added
hypotheses. Existing scalar recurrence lemmas supply the finite-time and
limsup conclusions once that bridge is proved. All construction definitions
have actual bodies; there are no construction placeholders or custom axioms.

## Supporting sources

`/spec/support/Research/` is empty. Its contents were copied unchanged into
`/workspace/Research/`; there were no supporting source files to copy.
