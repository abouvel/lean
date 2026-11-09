# Statement handoff

The initial statement is in `Submission.lean`. `lake build` succeeds. There is exactly one `sorry`, the proof of the full selected theorem; construction definitions have bodies. No `/spec/feedback.json` was present. There was no previous substantive Lean statement to revise. No selected conclusion or constant was revised.

## Source and explicit assumptions

- `Fin n ≃ Fin B × Fin T` records exactly the original ambient coordinates and a partition into size-T blocks. `T > 0`, `S > 0`, and `S ∣ n` make the algorithms meaningful. Zero ambient dimension is allowed. Each diagonal block is Mathlib `Matrix.PosDef`; nonsingularity of D must be derived, not assumed.
- `us ≥ 0`, `us < uc`, `(S+n/S-1)*us < 1`, and `(T+1)*uc < 1` state the precision and gamma domains. The remaining gamma domain follows from these.
- `Arithmetic` supplies only elementary relative-error laws, representing execution without overflow or underflow. Cholesky requires square root: its usual relative-error law is explicitly included, although the source common model lists only addition, subtraction, multiplication, and division. No Cholesky error bound is supplied as a hypothesis.
- `CholeskySuccessful` means that every actual intermediate radicand and rounded diagonal is positive. This interprets the source's already computed Cholesky factor; it does not assert that SPD by itself guarantees successful floating-point factorization. The supporting Cholesky-solve theorem also explicitly requires success. All computed factors are fixed and reused.
- `Conversion` models optional residual conversion to correction precision with its elementary relative-error law, as in the source proof's residual conversion term. The identity conversion is permitted. This is not a residual error certificate.
- The initial guess is arbitrary. A = D+N and A*x=b are explicit hypotheses. No invertibility of A, restriction q<1, backward-error certificate, scalar recurrence, or target error bound is assumed.
- `eta < 1` is unconditional for the theorem; `alpha < 1` conditions only the finite-iteration and limsup conclusions, exactly as in the selected statement.

## Construction conventions

Sequential sums start with the first entry, avoiding an unnecessary rounded addition to zero. Size-S tiles use original `Fin n` entries in order. The `S ∣ n` hypothesis guarantees the n/S tiles cover the vector. Empty dots in Cholesky and triangular substitution omit subtraction of zero. Upper-triangular Cholesky computes each row using earlier rows. Forward substitution uses the transpose; backward substitution visits coordinates in reverse order. The assembled factor is block diagonal in the original coordinates. The iterates are a natural-number recursion through the concrete rounded step.

`vectorInf` is the maximum absolute component and `matrixInf` the maximum absolute row sum; these are not Mathlib's default matrix norm. Both are zero in empty dimension. G uses the nonsingular matrix inverse of D, with its invertibility to be proved from the SPD blocks. All constants retain the source formulas and the full theorem uses these definitions directly.

## Remaining proof work

Prove the sequential tiled-dot gamma bound and Cholesky/triangular-solve backward-error bounds from the operation laws, then derive the componentwise residual and correction estimates. In particular, do not treat the supplied paper lemmas as assumptions. Establish nonnegativity of the constants and positivity of 1-eta before dividing. Preserve the update cancellation to obtain q rather than 1+q in alpha. Prove the affine recurrence consequences for every natural k, including zero, and justify the real limsup with boundedness and nonnegativity. Under alpha<1 establish positivity of 1-alpha before geometric-sum division.

The generic memory artifact `pilot-general-lean-001` was opened only for compiler/arithmetic notes. Its denominator-positivity advice influenced the explicit proof obligations above; it supplies no mathematical evidence for this statement. Memory retrieval used the index and direct artifact opening, with no search queries.

## Unchanged supporting sources

`Source/source.txt`, `Source/paper.tex`, `Source/references.bib`, and `Source/source.pdf` are byte-for-byte copies. The supplied `/spec/support/Research` directory was empty.
