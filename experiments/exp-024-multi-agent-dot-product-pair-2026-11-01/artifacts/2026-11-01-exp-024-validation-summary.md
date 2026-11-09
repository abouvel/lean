artifact_id: 2026-11-01-exp-024-validation-summary
date: 2026-11-01
project: exp-024-multi-agent-dot-product-pair-2026-11-01
status: failed
memory_mode: stateless
retrieved_artifacts: []
verification: See Evidence; repository gate `bash pipeline/verify.sh` also passed.
experiment_id: exp-024-multi-agent-dot-product-pair-2026-11-01
condition: stateless
task_id: multi-agent-dot-product-roundtrip-pilot
model: gpt-6.1-sol
reasoning_effort: medium
starting_commit: unknown
artifact_snapshot: batch-manifest.json (includes dirty runtime hashes/archive)
time_limit: {"planner": 90, "formalizer": 150, "prover": 180, "translator": 180, "judge": 180}
verification_command: bash pipeline/verify.sh
success: false

## Request

Implement the saved revision and work until it can be verified.

## Target

Exercise isolated roles, Lean acceptance boundaries, and round-trip semantic evaluation.
Expected labels remain host-only; no prior research-memory artifact is exposed to evaluators.

## Result

Both production conditions completed planner/formalizer/prover and built their Lean submission, but host augmentation of the verifier record failed due to container-owned mode-0644 outputs. This is an infrastructure failure, not a semantic rejection.

## Decisions and reasoning

Make trusted verification exports host-writable. Preserve this frozen pair and rerun both conditions from the same original task state.

## What worked

Formal preflight, candidate fingerprinting, preserved raw outputs, and fail-closed routing
allow mechanical failures and semantic defects to be distinguished.

## What failed

Both production conditions completed planner/formalizer/prover and built their Lean submission, but host augmentation of the verifier record failed due to container-owned mode-0644 outputs. This is an infrastructure failure, not a semantic rejection.

## Reusable observations

Make trusted verification exports host-writable. Preserve this frozen pair and rerun both conditions from the same original task state. This record is raw experiment evidence, not a promoted validated lesson.

## Evidence

[batch-manifest.json](../batch-manifest.json), [plan.json](../plan.json), [comparison.json](../comparison.json).

## Remaining limitations

Expert semantic adjudication is pending. Controlled development cases and a single
dot-product pair do not establish general evaluator accuracy or a memory advantage.
The supplied model/reasoning settings and budgets are recorded in frozen configuration;
unknown measurements remain unknown.

## Metrics

Available per-role timing and token data remain in raw metrics and scores; cost: unknown.
Distinct failed mathematical strategies: unknown. Aristotle calls: 0.
