# Source-only floating-point formalization in an isolated container

```text
artifact_id: run-2026-10-19-floating-point-stateless
date: 2026-10-19
project: binary-tree-reduction
status: verified
memory_mode: stateless
retrieved_artifacts: none
verification: full trusted offline build/scans passed; independent critic and compiled acceptance checks passed
experiment_id: 2026-10-19-binary-tree-pilot-gpt61
condition: stateless
task_id: sahil-theorem-3.1-algorithm-1
model: gpt-6.1-sol
reasoning_effort: medium
starting_commit: 66a6e9e85488743ca7f8adad84260103bcaddaa0
artifact_snapshot: frozen-manifest.json records paired snapshot; not mounted in this condition
time_limit: 1200 seconds
verification_command: bash pipeline/verify.sh
success: true
```

## Request

> wait. the first run doesn't recieve any lean instructions. can you execute this plan

## Target

Formalize Sahil Bhola's original Algorithm 1 and Theorem 3.1. The exact source
PDF and extracted mathematical proof were supplied, without a worked example,
Lean proof hints, theorem skeleton, prior code, artifacts, or chat context.

## Result

Completed an independent 490-line formalization. The general result covers
nonempty inputs, occurrence preservation, unchanged carries, exact logarithmic
depth, and the indexed componentwise gamma backward-error bound. Trusted
verification and the separate critic's compiled checks passed.

## Decisions and reasoning

The actor chose a direct numerical loop and a separate expression-tree model,
proved their equivalence, and transported perturbations back to original input
indices through list permutations. It used a proved gamma recurrence rather
than assuming a product-error lemma. See the actor's own decision log.

## What worked

Source-only instructions plus Mathlib and a fresh compiler environment were
sufficient for this task. The critic compiled the withheld five-input trace,
symbolic carry identities, duplicate/singleton checks, and a coordinatewise
specialization. The main theorems' axiom audit found only standard foundations.

## What failed

Initial denominator normalization, library names, indexing syntax, and an
existential binder needed compiler-guided repair. These were resolved. A prior
attempt on another model was capacity-interrupted and is preserved separately.

## Reusable observations

The result illustrates that formal correctness and source fidelity can be
checked separately without giving the builder a worked example. This is one
source-assisted task, not evidence of general capability or a learning gain.
No new shared validated lesson is promoted from this comparison.

## Evidence

- [Experiment report](../REPORT.md)
- [Proof](../stateless/workspace/Research/Submission.lean)
- [Exact prompt](../stateless/output/actual-prompt.txt)
- [Decisions](../stateless/output/decisions.md)
- [Verification](../stateless/evaluation/verification.json)
- [Critic](../stateless/review/review.json)

## Remaining limitations

Abstract deterministic relative-error model; no IEEE bit-level or probabilistic
result. Scalar theorem with coordinatewise use independently checked. No human
sign-off or critic-accuracy benchmark. One fixed-order run per condition.

## Metrics

```text
wall_time_seconds: 458.993
input_tokens: 1278341
cached_input_tokens: 1221248
output_tokens: 22111
reasoning_output_tokens: 8351
cost: unknown
compiler_command_events: 24
distinct_failed_strategies: unknown
aristotle_calls: 0
submitted_source_lines: 490
offline_verification_seconds: 14.871
critic_seconds: 107.994
semantic_review: independent critic pass; human sign-off not claimed
```
