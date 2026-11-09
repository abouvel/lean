artifact_id: 2026-11-01-exp-025-validation-summary
date: 2026-11-01
project: exp-025-verifier-export-canary-2026-11-01
status: verified
memory_mode: stateless
retrieved_artifacts: []
verification: See Evidence; repository gate `bash pipeline/verify.sh` also passed.
experiment_id: exp-025-verifier-export-canary-2026-11-01
condition: stateless
task_id: verifier-output-permission-canary
model: not applicable; no model call
reasoning_effort: not applicable
starting_commit: unknown
artifact_snapshot: candidate-verify.py; no research memory
time_limit: "unknown"
verification_command: bash pipeline/verify.sh
success: true

## Request

Implement the saved revision and work until it can be verified.

## Target

Exercise isolated roles, Lean acceptance boundaries, and round-trip semantic evaluation.
Expected labels remain host-only; no prior research-memory artifact is exposed to evaluators.

## Result

A real UID-1100 Docker verifier exported mode-0666 JSON/log files; the host successfully rewrote both. No model call was used. The shell build was a stub: this test makes no mathematical verification claim.

## Decisions and reasoning

Exercise actual container/host ownership boundaries in addition to unit tests.

## What worked

Formal preflight, candidate fingerprinting, preserved raw outputs, and fail-closed routing
allow mechanical failures and semantic defects to be distinguished.

## What failed

No failure in the declared controlled acceptance test. Earlier failures remain in their original experiments.

## Reusable observations

Exercise actual container/host ownership boundaries in addition to unit tests. This record is raw experiment evidence, not a promoted validated lesson.

## Evidence

[canary.py](../canary.py), [result.json](../result.json).

## Remaining limitations

Expert semantic adjudication is pending. Controlled development cases and a single
dot-product pair do not establish general evaluator accuracy or a memory advantage.
The supplied model/reasoning settings and budgets are recorded in frozen configuration;
unknown measurements remain unknown.

## Metrics

Available per-role timing and token data remain in raw metrics and scores; cost: unknown.
Distinct failed mathematical strategies: unknown. Aristotle calls: 0.
