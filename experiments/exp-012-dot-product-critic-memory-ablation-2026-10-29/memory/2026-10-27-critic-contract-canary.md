# Live critic contract canary

```text
artifact_id: 2026-10-27-critic-contract-canary
date: 2026-10-27
project: critic-report-contract-canary
status: verified
memory_mode: stateless
retrieved_artifacts: []
verification: bash pipeline/verify.sh — passed (8,036 jobs; placeholder/custom-axiom scans passed)

experiment_id: exp-005-critic-canary-2026-10-27
condition: stateless
task_id: critic-report-contract-canary
model: gpt-6.1-sol
reasoning_effort: medium
starting_commit: a42eeb51fa8a9ee36f5a6027bd840189198ab283
artifact_snapshot: sha256:57e35766f5e39e97db2691fdf887c41c8a5cceaea625ae0eba9553e66ed4804f
time_limit: 240 seconds per critic
verification_command: bash pipeline/verify.sh
success: true
```

## Request

Test the revised critic report contract with live model sessions after explicit
approval to send the frozen rubric, source, candidates, and verification logs to
the configured OpenAI model service.

## Target

Preserve the exact acceptance tests:

1. A known-incomplete candidate produces only a valid completeness-phase
   `checkpoint.json` rejection and is stopped by the checkpoint watcher.
2. A known-complete candidate produces only a valid final-phase passing
   `review.json` and exits cleanly.

## Result

Both acceptance tests passed. The incomplete candidate was rejected for failing
to connect returned tree leaves to the original input occurrences. The complete
candidate passed full semantic review, and the critic compiled independent Lean
checks in its private output directory.

## Decisions and reasoning

This was registered as an infrastructure canary rather than a new proof attempt
or memory-ablation comparison. The two candidates were frozen before the calls,
their expected statuses were declared in advance, and the active controller's
`completed_review` validator—not manual reinterpretation—decided success.

## What worked

- The incomplete path wrote `checkpoint.json`, set `stopped_for_checkpoint`,
  omitted `review.json`, and returned an actionable semantic rejection.
- The complete path omitted `checkpoint.json`, wrote a typed final `review.json`,
  passed every requirement, reported no missing obligations, and exited normally.
- Neither report used `null` corrections or the wrong phase/filename.
- The repository verification gate passed after the canary.

## What failed

No acceptance test failed. An initial launch was blocked until the user explicitly
approved the external transfer; no rubric or candidate was sent during that
blocked attempt. A prior connectivity smoke sent only `READY`.

## Reusable observations

The revised typed examples and process-state routing worked on both terminal
paths in this canary. This is evidence that the report contract is operational,
not evidence that critic judgments are universally accurate.

## Evidence

- [Structured comparison](../comparison.json)
- [Frozen manifest](../frozen-manifest.json)
- [Incomplete checkpoint](../canary-incomplete/review/checkpoint.json)
- [Incomplete metrics](../canary-incomplete/review/metrics.json)
- [Complete final review](../canary-complete/review/review.json)
- [Complete metrics](../canary-complete/review/metrics.json)
- [Independent Lean check](../canary-complete/review/Independent.lean)
- Raw events, prompts, stderr, and container logs remain under each `review/` directory.

## Remaining limitations

- This uses two known candidates, not unseen or adversarial examples.
- Critic accuracy and calibration still require a larger human-labeled set.
- The complete critic's `time.time`-derived wall metric was 248.758 seconds even
  though the monotonic 240-second controller did not record a timeout; treat that
  wall-clock number cautiously.
- Monetary cost is unknown. No claim about retrieval benefit or model learning is made.

## Metrics

| Metric | Incomplete | Complete |
| --- | ---: | ---: |
| Controller result | expected fail checkpoint | expected final pass |
| Reported wall time | 26.074 s | 248.758 s |
| Compiler-command events | 0 | 6 |
| Input tokens | unknown | 584,536 |
| Cached input tokens | unknown | 520,320 |
| Output tokens | unknown | 5,465 |
| Reasoning-output tokens | unknown | 1,274 |
| Aristotle calls | 0 | 0 |
| Final candidate size | 318 lines | 490 lines |
| Distinct failed strategies | unknown | unknown |
| Semantic review passed | no, expected rejection | yes |

Token usage for the checkpoint-stopped critic is unavailable because the process
terminated before a final usage event. Cost is unknown and was not estimated.
