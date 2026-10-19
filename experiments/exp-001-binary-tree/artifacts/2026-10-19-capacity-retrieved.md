# Retrieved proof attempt prevented by model capacity

```text
artifact_id: run-2026-10-19-capacity-retrieved
date: 2026-10-19
project: binary-tree-reduction
status: failed
memory_mode: retrieved
retrieved_artifacts: none; actor stopped before retrieval
verification: bash pipeline/verify.sh; import-only scaffold compiled but is not a proof
experiment_id: 2026-10-19-binary-tree-pilot
condition: retrieved
task_id: sahil-theorem-3.1-algorithm-1
model: gpt-5.6-sol
reasoning_effort: medium
starting_commit: 66a6e9e85488743ca7f8adad84260103bcaddaa0
artifact_snapshot: frozen-manifest.json; pilot-general-lean-001 available read-only
time_limit: 1200 seconds
verification_command: bash pipeline/verify.sh
success: false
failure_class: model_service_capacity
```

## Request

> wait. the first run doesn't recieve any lean instructions. can you execute this plan

## Target

Same original source-assisted formalization task as the paired stateless actor,
with a read-only generic memory snapshot additionally available.

## Result

The service returned `Selected model is at capacity. Please try a different model.`
before the actor used tools or wrote a proof. The unchanged import-only scaffold
compiled, but the trusted evaluator explicitly rejected it as an empty submission.

## Decisions and reasoning

Retain this failure and any model fallback as separate experiments. Do not infer
that retrieval improved or harmed performance from an actor that never began.

## What worked

Memory visibility and access-control preflight passed. The scaffold built offline.

## What failed

The model service could not start the substantive attempt.

## Reusable observations

Build success alone cannot distinguish an actual theorem proof from an empty
project. Semantic and nontrivial-submission checks are necessary.

## Evidence

- [Frozen inputs](../interrupted/frozen-manifest.json)
- [Metrics](../interrupted/retrieved/output/metrics.json)
- [Transcript](../interrupted/retrieved/output/events.jsonl)
- [Verification](../interrupted/retrieved/evaluation/verification.json)

## Remaining limitations

No retrieval, substantive proof attempt, critic review, or learning conclusion.
The available snapshot was manually curated; it is not evidence of autonomous learning.

## Metrics

```text
wall_time_seconds: 3.530
tokens: unknown
cost: unknown
compiler_command_events: 0
distinct_failed_strategies: unknown
aristotle_calls: 0
submitted_source_lines: 1
semantic_review: no theorem submitted
```
