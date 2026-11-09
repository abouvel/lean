artifact_id: 2026-11-01-exp-022-validation-summary
date: 2026-11-01
project: exp-022-construction-roundtrip-calibration-2026-11-01
status: verified
memory_mode: stateless
retrieved_artifacts: []
verification: See Evidence; repository gate `bash pipeline/verify.sh` also passed.
experiment_id: exp-022-construction-roundtrip-calibration-2026-11-01
condition: stateless
task_id: multi-agent-dot-product-roundtrip-pilot
model: gpt-6.1-sol
reasoning_effort: medium
starting_commit: b5df08f54d45608c2aad01a58ac3dee5ff95d8f6
artifact_snapshot: frozen-manifest.json (includes dirty runtime hashes/archive)
time_limit: {"planner": 150, "formalizer": 150, "prover": 150, "translator": 150, "judge": 150}
verification_command: bash pipeline/verify.sh
success: true

## Request

Implement the saved revision and work until it can be verified.

## Target

Exercise isolated roles, Lean acceptance boundaries, and round-trip semantic evaluation.
Expected labels remain host-only; no prior research-memory artifact is exposed to evaluators.

## Result

Schema-2 construction calibration: 3/3 correct. Explicit expression accepted; existence-only and abstract choice rejected. No false pass or rejection on these controlled cases.

## Decisions and reasoning

Construction policy is task-specific. Classical reasoning in a proof is allowed; abstract selection is insufficient when an explicit expression is required.

## What worked

Formal preflight, candidate fingerprinting, preserved raw outputs, and fail-closed routing
allow mechanical failures and semantic defects to be distinguished.

## What failed

No failure in the declared controlled acceptance test. Earlier failures remain in their original experiments.

## Reusable observations

Construction policy is task-specific. Classical reasoning in a proof is allowed; abstract selection is insufficient when an explicit expression is required. This record is raw experiment evidence, not a promoted validated lesson.

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
