artifact_id: 2026-11-05-initial-overnight-startup-failure
date: 2026-11-05
project: three-family overnight pilot
status: failed
memory_mode: stateless
retrieved_artifacts: []
verification: candidate verification did not complete
experiment_id: exp-028-three-family-overnight-2026-11-05
condition: stateless
task_id: multi-agent-dot-product-roundtrip-pilot
model: gpt-6.1-sol
reasoning_effort: medium
starting_commit: b5df08f54d45608c2aad01a58ac3dee5ff95d8f6
artifact_snapshot: batch-manifest.json and per-job frozen manifests
time_limit: 120 seconds for Lean preflight, 3600 seconds per job
verification_command: bash pipeline/verify.sh
success: false

## Request

Run the three-family pilot overnight.

## Target

One job with and one without frozen memory for each of dot product, Horner
evaluation, and forward finite differences.

## Result

The first dot-product worker timed out on the offline Lean smoke build.
The Horner worker reached the planner before the coordinator was stopped.
The remaining jobs were unrun in this batch.

## Decisions and reasoning

The restart preserves matched conditions. The fresh batch raises the
per-container RAM limit from 8 to 12 GiB for all six jobs. Mathematical inputs,
the memory snapshot, and time budgets are the same.

## What worked

The coordinator preserved the startup failure. A subsequent worker completed
preflight and connectivity before interruption.

## What failed

The initial Lean smoke build exceeded the fixed 120-second startup timeout.
The evidence does not establish the exact cause of the slowdown.

## Reusable observations

Keep startup failures separate from proof and semantic outcomes. Retain frozen
inputs and raw results when retrying a matched pilot.

## Evidence

[Job results](jobs.md) and [replacement batch](../../exp-030-three-family-overnight-2026-11-05/plan.json).

## Remaining limitations

The first batch supplies no paired comparison. Expert review is pending.

## Metrics

Preflight timeout was 120 seconds. Cost, total tokens, and isolated proof size
are unknown. Aristotle was disabled.
