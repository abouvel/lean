artifact_id: 2026-11-01-exp-020-validation-summary
date: 2026-11-01
project: exp-020-roundtrip-calibration-2026-11-01
status: failed
memory_mode: stateless
retrieved_artifacts: []
verification: See Evidence; repository gate `bash pipeline/verify.sh` also passed.
experiment_id: exp-020-roundtrip-calibration-2026-11-01
condition: stateless
task_id: floating-point-dot-product-critic-benchmark
model: gpt-6.1-sol
reasoning_effort: medium
starting_commit: b5df08f54d45608c2aad01a58ac3dee5ff95d8f6
artifact_snapshot: frozen-manifest.json (includes dirty runtime hashes/archive)
time_limit: {"planner": 180, "formalizer": 180, "prover": 180, "translator": 180, "judge": 180}
verification_command: bash pipeline/verify.sh
success: false

## Request

Implement the saved revision and work until it can be verified.

## Target

Exercise isolated roles, Lean acceptance boundaries, and round-trip semantic evaluation.
Expected labels remain host-only; no prior research-memory artifact is exposed to evaluators.

## Result

The first export-permission fix tried to chmod a host-owned directory and failed. No terminal judge verdict was obtained.

## Decisions and reasoning

Normalize only container-owned files; a real UID-boundary canary passed before exp-021.

## What worked

Formal preflight, candidate fingerprinting, preserved raw outputs, and fail-closed routing
allow mechanical failures and semantic defects to be distinguished.

## What failed

The first export-permission fix tried to chmod a host-owned directory and failed. No terminal judge verdict was obtained.

## Reusable observations

Normalize only container-owned files; a real UID-boundary canary passed before exp-021. This record is raw experiment evidence, not a promoted validated lesson.

## Evidence

[protocol.json](../protocol.json), [frozen-manifest.json](../frozen-manifest.json), [FAILED.md](../FAILED.md).

## Remaining limitations

Expert semantic adjudication is pending. Controlled development cases and a single
dot-product pair do not establish general evaluator accuracy or a memory advantage.
The supplied model/reasoning settings and budgets are recorded in frozen configuration;
unknown measurements remain unknown.

## Metrics

Available per-role timing and token data remain in raw metrics and scores; cost: unknown.
Distinct failed mathematical strategies: unknown. Aristotle calls: 0.
