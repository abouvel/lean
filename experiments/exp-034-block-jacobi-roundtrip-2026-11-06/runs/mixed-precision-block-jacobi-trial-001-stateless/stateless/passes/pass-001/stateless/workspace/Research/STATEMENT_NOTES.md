# Statement handoff

The authoritative statement is `/spec/source.txt`; the exact source, full paper,
and bibliography have been copied unchanged to this directory. The supplied
`/spec/support/Research` directory contains no files. `/spec/feedback.json` was
absent. This is the initial statement skeleton: there is no earlier statement
or feedback-driven revision.

The target is
`MixedPrecisionBlockJacobi.mixed_precision_update_form_block_jacobi_in_floating_point_arithmetic`.
Its only `sorry` is its theorem proof, intentionally left for the proving role.
All construction definitions have actual bodies. No backward-error estimate,
algorithmic norm bound, or error recurrence is a hypothesis.

## Source interpretation and explicit assumptions

* `layout : Fin n ≃ Fin B × Fin T` expresses an actual partition into complete
  T-sized blocks, allowing arbitrary coordinate order. `blockDiagonal layout
  blocks` is D. Every block is positive definite over the reals (and hence
  symmetric). No invertibility of A or contraction assumption on q is added.
  Positive tile and block sizes are explicit; empty ambient dimensions are also
  supported, with zero norms. The layout implies n = B*T. S divides n.
* The precisions satisfy 0 ≤ us < uc. The explicit validity conditions are
  `(S+n/S-1)*us < 1` and `(T+1)*uc < 1`; validity of `gamma T uc` follows.
  `gamma`, `c₁`, `c₂`, `gain`, `eta`, `q`, `p`, `alpha`, and `beta` have precisely
  the displayed source formulas. D⁻¹ is Mathlib's genuine matrix inverse, whose
  inverse identities must be derived from block SPD by the proving role.
* A tape assigns a separate relative error to each scalar operation address.
  `Execution.Admissible` bounds them at the appropriate precision for every
  block, iteration, and component. `rounded` computes z*(1+delta). This is the
  source's real-valued standard rounding model in the absence of overflow or
  underflow. It does not impose global backward-error conclusions. Separate
  tape prefixes distinguish products, accumulation, subtraction, division,
  square root, residual conversion, and solution update. Matvec reduction
  excludes additions to an artificial zero, preserving the exact gamma index.
* Cholesky is the upper-triangular column recurrence printed in the paper,
  using sequential inner products, subtraction, division, and square root.
  It returns `none` on nonpositive radicands or zero divisors. `hsuccess` means
  all computed block factors actually exist. This unpacks the selected
  statement's reference to computed Cholesky factors and the earlier helper's
  explicit successful-completion premise. SPD alone is not asserted to ensure
  floating-point success. Factors are computed once and reused.
* The source's displayed elementary rounding model names +,-,*,/ but its
  Cholesky recurrence also uses square roots. Here floating-point Cholesky is
  interpreted to include the standard relative-error model
  `fl(sqrt(d)) = sqrt(d)*(1+delta)`, |delta| ≤ uc, for positive d. This is the
  ordinary no-underflow correctly rounded square-root interpretation required
  by the cited Cholesky analysis, now explicit in `cholDiagonal` and the tape
  admissibility premise. The model permits all such local errors; it does not
  assume the desired factorization bound. If the source is instead read as
  giving no rounding guarantee at all for sqrt, its Cholesky helper and selected
  result need that missing specification; no such theorem follows from only
  unconstrained square roots.
* The matrix and vector inputs are the source's real inputs, with no extra
  unbudgeted input-conversion perturbation. Residual conversion to uc is
  explicitly executed componentwise, as used in the paper's proof. A zero error
  represents exact conversion. First-row Cholesky/substitution kernels avoid a
  spurious subtraction of zero.
* `vectorInfNorm` is the maximum absolute component. `matrixInfNorm` is the
  maximum absolute row sum, independent of Mathlib's default matrix norm.
  `error` refers to the recursively constructed `iterates`, never an arbitrary
  sequence postulated to satisfy a recurrence. The theorem gives the one-step
  inequality for every k; only the finite-time and real limsup conclusions
  require alpha < 1. The proving role must justify boundedness for real limsup.

## Outstanding proof obligations

Prove the selected target from these operational definitions. In particular,
derive tiled matvec backward error and Cholesky/substitution backward error
from admissible local operations; assemble blocks; derive nonsingularity and
inverse identities from SPD; derive the stated recurrence with the exact alpha
and beta; then prove its finite-time and actual-error limsup consequences.
There are no helper bounds assumed or supplied as proved facts in this skeleton.

## Validation

`lake build` completed successfully (8028 jobs). Its only warning is the
intentional final theorem proof `sorry`. An additional Lean audit checked by
`rfl` that gain, p, and beta use the inverse of D, and checked that the iterates,
computed factors, and both norm definitions have no `sorryAx` dependency.
The three copied source files were compared byte for byte with their originals.
`/output/statement.json` was written atomically and its schema and names checked.

## Proving pass status

This pass added proved helpers in `Submission.lean` for local tape bounds,
finite products (including direct/inverse rounding factors), sequential
accumulation and dot-product forward error, the genuine infinity norms,
nonnegativity of the constants, block-diagonal nonsingularity and both inverse
identities, residual perturbations conditional on a matvec estimate, residual
conversion and rounded solution addition. Scalar feedback absorption and the
finite-time and actual-sequence limsup conclusions from a recurrence are proved.

The exported theorem now invokes those scalar consequences, but its local
`hstep` still contains the original unresolved proof obligation, as one `sorry`.
In particular, no tiled-matvec or Cholesky backward-error theorem is supplied as
an assumption. The project is NOT a completed proof. See `/output/final.md` for
the precise remaining obligations and compilation/axiom audit results.
