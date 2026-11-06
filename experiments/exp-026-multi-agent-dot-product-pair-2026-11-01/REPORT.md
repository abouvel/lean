# Separate-agent pipeline implementation and verification

Updated: 2026-11-01. Branch: `codex/modular-proof-pipeline`.

## What changed

The opt-in revision uses five fresh model sessions: planner, formalizer, prover,
blind Lean-to-mathematics translator, and source-versus-translation judge.
The existing direct critic runs independently during calibration. Historical
configurations retain their existing builder/verifier/critic workflow.

The deterministic harness freezes inputs and runtime, validates handoffs, builds
the Lean project, scans placeholders, audits transitive axioms, protects supplied
sources and formalizer declarations, fingerprints candidates, validates reports,
routes acceptance/repair/human review, and records every invoked role's metrics.
The prover may add helpers and complete proofs but cannot silently change the
formalizer's theorem types or construction bodies.

Only retrieved production agents receive the frozen memory snapshot. Neither
semantic evaluation agent receives research memory, production conversation,
condition labels, or the other evaluator's verdict. The translator receives a
dependency bundle extracted from elaborated Lean declarations, without source
comments or theorem proof bodies. The judge receives the source, task contract,
and blind translation. These are controlled input boundaries, not a claim of
adversarially hardened anonymity.

Translation schema 1 covers every selected target and construction. Judgment
schema 2 separates implication from delivery and construction completeness;
mathematically recoverable supporting lemmas do not count as an already completed
Lean theorem. Missing context or evaluator disagreement stops acceptance.

## Automated checks

- 86 Python regression tests pass, including all legacy tests, blinded role
  inputs, handoffs, statement protection, candidate hashes, invalid passes,
  disagreement routing, export permissions, and failed-run role accounting.
- `bash pipeline/verify.sh` passes on the repository: full Lean build and both
  placeholder/custom-axiom source scans.
- A private-axiom canary passed the older compilation/source-scan gate but was
  rejected by the new elaborated dependency audit. Evidence:
  [audit](../exp-018-roundtrip-calibration-2026-11-01/axiom-canary/formal-audit/dependency-canary/audit.json).
- Actual Docker UID-boundary canaries tested model output and trusted verifier
  exports. These are permission tests, not mathematical proof tests.

## Evaluator development results

| Experiment | Result | Interpretation |
| --- | --- | --- |
| [Initial six-case calibration](../exp-021-roundtrip-calibration-2026-11-01/summary.json) | 5/6 correct; one false pass | The judge composed partial results mentally and credited a missing final Lean theorem. The direct critic caught it; acceptance stopped. |
| [Delivery follow-up](../exp-023-roundtrip-delivery-followup-2026-11-01/summary.json) | 6/6 correct; zero false passes/rejections | Fresh schema-2 judges reused the same blind translations. Development evidence, not held-out accuracy. |
| [Construction calibration](../exp-022-construction-roundtrip-calibration-2026-11-01/summary.json) | 3/3 correct | Explicit answer accepted; existence-only and abstract choice rejected under an explicit-expression contract. |

The six dot-product cases cover a complete proof, renamed complete proof,
proposition without proof, additions-only partial result, zero-unit-roundoff-only
restriction, and conclusion assumed as a premise. Hidden expected labels were
never supplied to the agents. Raw prompts, reports, metrics, and frozen manifests
remain with each experiment. The initial false pass was retained rather than
relabeled after seeing the result.

## Live dot-product integration

Both frozen conditions completed all five isolated roles, the independent
direct critic, and trusted verification; both were accepted. The final axiom
audits found no unapproved axioms, changed protected files, or changed formalizer
declarations. Both semantic evaluators passed each final candidate.

| Condition | Outcome | Passes | Proof-loop wall seconds | Total model seconds | Model sessions |
| --- | --- | --- | --- | --- | --- |
| stateless | accepted | 1 | 382.065 | 310.604 | 6 |
| retrieved | accepted | 1 | 404.828 | 328.767 | 6 |

[stateless submission](runs/dot-product-trial-001-stateless/stateless/passes/pass-001/stateless/workspace/Research/Submission.lean), [retrieved submission](runs/dot-product-trial-001-retrieved/retrieved/passes/pass-001/retrieved/workspace/Research/Submission.lean).

Retrieved artifact IDs actually opened: `pilot-general-lean-001`. Recorded decisions influenced: 0. See the [structured retrieval log](runs/dot-product-trial-001-retrieved/retrieved/passes/pass-001/retrieved/output/retrieval.json). Costs remain unknown. Wall time includes verification and local overhead; total model seconds sums model stages, including direct criticism.

See [comparison](comparison.json), [frozen plan](plan.json), and per-condition pass records for complete measured metrics.


The task supplies the same five proved prerequisites to both conditions and
requires construction of exact-product and rounded-product trees, a rounded
dot-product reduction, and the full componentwise backward-error theorem. It uses
an abstract real relative-rounding model, not executable IEEE arithmetic.

Only generic `pilot-general-lean-001` guidance is in the retrieved snapshot. The
completed target theorem/proof and other-condition outputs are excluded. One
matched pair is an integration test; it cannot establish a memory advantage.
Order is stateless first, and model/service/cache timing can confound comparisons.

## Failures preserved

- `exp-018`: a model's atomically created private output was unreadable by the host.
- `exp-020`: the first permission normalization tried to chmod a host-owned directory.
- `exp-021`: the semantic false pass described above.
- `exp-024`: both dot-product submissions compiled, but host audit augmentation
  failed on container-owned verifier exports. Both outcomes are infrastructure
  errors. The tested fix exports trusted JSON/log files with host-writable modes;
  [exp-025](../exp-025-verifier-export-canary-2026-11-01/result.json) exercises the real boundary.

Fresh experiments were created after fixes; frozen runs were not rewritten.

## Usage and remaining work

See [configuration and module guide](../../pipeline/ROUNDTRIP.md) and the
[saved research plan](../../pipeline/REVISION_PLAN.md). A reusable dot-product
template is [exp-019](../exp-019-multi-agent-dot-product-task-2026-11-01/batch.json).
Choose a new experiment name for each fresh batch:

```bash
python3 pipeline/batch.py plan \
  --spec experiments/exp-019-multi-agent-dot-product-task-2026-11-01/batch.json \
  --name <new-experiment-id>
python3 pipeline/batch.py run --experiment experiments/<new-experiment-id>
```

The implementation intentionally supports calibration mode only. A Lean-experienced
reviewer still needs to adjudicate disagreements and sample passes/rejections,
and the advisor must approve task/prerequisite boundaries and accuracy thresholds
before a larger study. The proposed three-task, three-trial, two-condition study
has not been run. No lessons from these runs are automatically promoted into
future memory. Available timings/tokens are recorded; unavailable costs and
measurements remain `unknown`.
