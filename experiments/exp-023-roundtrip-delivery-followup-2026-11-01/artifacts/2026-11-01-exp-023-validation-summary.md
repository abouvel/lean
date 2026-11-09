artifact_id: 2026-11-01-exp-023-validation-summary
date: 2026-11-01
project: exp-023-roundtrip-delivery-followup-2026-11-01
status: verified
memory_mode: stateless
retrieved_artifacts: []
verification: See Evidence; repository gate `bash pipeline/verify.sh` also passed.
experiment_id: exp-023-roundtrip-delivery-followup-2026-11-01
condition: stateless
task_id: floating-point-dot-product-critic-benchmark
model: gpt-6.1-sol
reasoning_effort: medium
starting_commit: b5df08f54d45608c2aad01a58ac3dee5ff95d8f6
artifact_snapshot: frozen-manifest.json (includes dirty runtime hashes/archive)
time_limit: {"planner": 180, "formalizer": 180, "prover": 180, "translator": 180, "judge": 180}
verification_command: bash pipeline/verify.sh
success: true

## Request

Implement the saved revision and work until it can be verified.

## Target

Exercise isolated roles, Lean acceptance boundaries, and round-trip semantic evaluation.
Expected labels remain host-only; no prior research-memory artifact is exposed to evaluators.

## Result

Development follow-up: 6/6 correct, no false passes or rejections. Reused blind translations from exp-021; only the schema-2 judge was rerun. This is not held-out accuracy.

## Decisions and reasoning

The judge now records implication, delivery completeness, construction completeness, and missing formal steps separately.

## What worked

Formal preflight, candidate fingerprinting, preserved raw outputs, and fail-closed routing
allow mechanical failures and semantic defects to be distinguished.

## What failed

No failure in the declared controlled acceptance test. Earlier failures remain in their original experiments.

## Reusable observations

The judge now records implication, delivery completeness, construction completeness, and missing formal steps separately. This record is raw experiment evidence, not a promoted validated lesson.

## Evidence

[protocol.json](../protocol.json), [frozen-manifest.json](../frozen-manifest.json), [scores](../scores.json), [summary](../summary.json).

## Remaining limitations

Expert semantic adjudication is pending. Controlled development cases and a single
dot-product pair do not establish general evaluator accuracy or a memory advantage.
The supplied model/reasoning settings and budgets are recorded in frozen configuration;
unknown measurements remain unknown.

## Metrics

Available per-role timing and token data remain in raw metrics and scores; cost: unknown.
Distinct failed mathematical strategies: unknown. Aristotle calls: 0.
