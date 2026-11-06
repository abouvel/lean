artifact_id: 2026-11-06-binary-tree-roundtrip-control
date: 2026-11-06
project: binary-tree-roundtrip-control
status: verified
memory_mode: stateless
retrieved_artifacts: []
verification: both fixture builds, source scans, and transitive axiom audits passed
experiment_id: exp-031-binary-tree-roundtrip-control-2026-11-06
condition: stateless
task_id: binary-tree-theorem-3.1-roundtrip-control
model: gpt-6.1-sol
reasoning_effort: medium
starting_commit: 37fc2b145b910e670a3b1256007d8da4d30bfc4a
artifact_snapshot: [frozen input hashes](../frozen-manifest.json)
time_limit: translator 180 s, judge 180 s, direct critic 240 s
verification_command: bash pipeline/verify.sh
success: true

## Request

Run a controlled binary-tree reduction test before launching the full study.

## Target

Exercise both semantic reviewers on the existing Algorithm 1 and Theorem 3.1
fixtures. Both must pass Lean. Only the fixture delivering the final theorem
about the original input occurrences should pass semantic review.

## Result

| Frozen fixture | Expected semantic verdict | Lean | Direct critic | Round trip | Elapsed seconds |
| --- | --- | --- | --- | --- | ---: |
| known-complete | pass | pass | pass | pass | 484.8 |
| missing-original-input-link | fail | pass | fail | fail | 294.1 |

## Decisions and reasoning

The fixtures had neutral IDs in the run. The harness kept the expected verdicts
outside the evaluator inputs. The standalone control invoked the same formal
and semantic checks as the study while holding the candidate Lean files fixed.

## What worked

The complete fixture was accepted. The incomplete fixture was rejected
semantically even though Lean verified the narrower claim.

## What failed

No frozen acceptance test failed. The negative fixture's missing original-input
link was intentional.

## Reusable observations

Report formal verification and semantic verdicts separately. These two labeled
fixtures provide an integration control before a broader batch. No lesson was
promoted to research memory.

## Evidence

[Protocol](../protocol.json), [scorecard](../scorecard.json),
and the [complete](../case-01/result.json) and [incomplete](../case-02/result.json)
structured reports.

## Remaining limitations

The controls use known repository fixtures, with no production-agent run and
no independent human adjudication. They provide no estimate of evaluator
accuracy on fresh cases or of a memory effect.

## Metrics

Per-reviewer wall time, model settings, tokens, and requirement-level evidence
are in the scorecard. Proof-production time and tokens are inapplicable.
Monetary cost is unknown.
