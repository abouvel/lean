# Stateless proof attempt interrupted by model capacity

```text
artifact_id: run-2026-10-19-capacity-stateless
date: 2026-10-19
project: binary-tree-reduction
status: partial
memory_mode: stateless
retrieved_artifacts: none
verification: bash pipeline/verify.sh; candidate did not pass
experiment_id: 2026-10-19-binary-tree-pilot
condition: stateless
task_id: sahil-theorem-3.1-algorithm-1
model: gpt-5.6-sol
reasoning_effort: medium
starting_commit: 66a6e9e85488743ca7f8adad84260103bcaddaa0
artifact_snapshot: unavailable to this condition; experiment frozen-manifest.json records the paired snapshot
time_limit: 1200 seconds
verification_command: bash pipeline/verify.sh
success: false
failure_class: model_service_capacity
```

## Request

> wait. the first run doesn't recieve any lean instructions. can you execute this plan

## Target

Formalize the original Algorithm 1 and Theorem 3.1 from Sahil Bhola's source.
The actor received the source's mathematical proof and pseudocode, no Lean
theorem skeleton, proof hints, worked example, prior chat, or existing solution.

## Result

The isolated actor began an implementation but the service ended the attempt
with `Selected model is at capacity. Please try a different model.`
The candidate did not pass the independent offline build. This is an
interrupted attempt, not evidence that the mathematics is beyond the model.

## Decisions and reasoning

Preserve this attempt. Use a separately named paired experiment for any model
fallback; do not silently switch models or combine the results.

## What worked

Docker isolation, model authentication, source delivery, and local Lean commands.

## What failed

Model service capacity interrupted the attempt after 156.308 seconds.
An earlier patch command also failed because it targeted one file twice.
The login shell required discovering the full path to the Lean binaries.

## Reusable observations

Distinguish service interruption from mathematical failure. A connectivity-only
model request does not guarantee that a longer proof session will remain available.
These observations are not promoted as validated proof lessons.

## Evidence

- [Frozen inputs](../../experiments/memory-ablation/2026-10-19-binary-tree-pilot/frozen-manifest.json)
- [Actor metrics](../../experiments/memory-ablation/2026-10-19-binary-tree-pilot/stateless/output/metrics.json)
- [Transcript](../../experiments/memory-ablation/2026-10-19-binary-tree-pilot/stateless/output/events.jsonl)
- [Verification](../../experiments/memory-ablation/2026-10-19-binary-tree-pilot/stateless/evaluation/verification.json)

## Remaining limitations

No completed proof, independent critic review, measured savings, or learning conclusion.

## Metrics

```text
wall_time_seconds: 156.308
tokens: unknown
cost: unknown
compiler_command_events: 4
distinct_failed_strategies: unknown
aristotle_calls: 0
submitted_source_lines: 144
semantic_review: incomplete candidate; no acceptance
```
