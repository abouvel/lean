Statement revision record: initial statement; no prior formal statement was revised.
/spec/feedback.json was absent, so there were no feedback-driven revisions.

The authoritative selected lemma is represented by
Research.TriangularUpdate.triangular_update in Submission.lean.
The statement uses the explicitly constructed perturbation, which in particular
supplies the existence of a single vector required in the source. It keeps
all k components, the exact gamma_k constant, b_k nonzero, k >= 2, and k*u < 1.
Nonnegative u is the standard unit-roundoff convention from the source model.

The real error trace quantifies over every permitted execution under the
standard relative-error model (the no-overflow/no-underflow assumption).
Only actual additions after the initial rounded product have bounded errors;
the unused addError at index zero is unconstrained. For k = 2, the accumulator
is exactly the one rounded product and the coefficient's addition product is
empty. With u = 0 all executed error terms are zero. The final coefficient is
the inverse of the product of the subtraction and division rounding factors.
No desired accumulated-error bound is assumed.

All construction definitions have bodies. The sole sorry is the proof of the
final theorem, intentionally left for the next proving role. There are no
custom axioms or other admitted helper lemmas.

The supplied /spec/support tree contains no files. The original paper.tex,
references.bib, source.txt, and source.pdf are copied unchanged to Sources/.
