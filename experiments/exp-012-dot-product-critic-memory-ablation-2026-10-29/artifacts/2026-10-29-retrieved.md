# Retrieved dot-product critic condition

artifact_id: `2026-10-29-dot-product-critic-retrieved`
date: 2026-10-29
project: Lean critic memory ablation
status: verified
memory_mode: retrieved
retrieved_artifacts: `[2026-10-27-critic-contract-canary, 2026-10-28-critic-agent-stable-ids]`
verification: all six condition gates passed; 60 pipeline tests passed; `bash pipeline/verify.sh` passed 8,036 jobs and placeholder/custom-axiom scans.

experiment_id: `exp-012-dot-product-critic-memory-ablation-2026-10-29`
condition: retrieved
task_id: `floating-point-dot-product-critic-memory-ablation`
model: `gpt-6.1-sol`
reasoning_effort: medium
starting_commit: `a42eeb51fa8a9ee36f5a6027bd840189198ab283`
artifact_snapshot: `frozen-manifest.json` SHA-256 `1655cbbb439ca5eee67989cfa7d43199502b49e5f7cb04e557435831ab489538`
time_limit: 240 seconds per critic
verification_command: `bash pipeline/verify.sh <condition>/evaluation-workspace`
success: true

## Request

Rerun the stateful/retrieved and stateless critic architecture on the floating-point dot-product proof.

## Target

Classify the same two complete and four compiling defective dot-product
candidates as the stateless condition, with access only to a frozen approved
snapshot of three general critic artifacts that predate and exclude the
dot-product benchmark and its answers.

## Result

The condition achieved 6/6 correct verdicts and found 4/4 expected defect
categories, with no false passes, false rejections, invalid reports, or
timeouts. Every run wrote a valid retrieval log and opened an approved artifact.

## Decisions and reasoning

The snapshot included three pre-dot-product critic artifacts. Actual logs show
that critics opened the contract-canary and stable-ID artifacts; none opened
the older five-case benchmark. Logged influence concerned checkpoint routing
and stable-ID/report coverage. Mathematical judgments were recorded as coming
from direct candidate inspection.

## What worked

- Both complete candidates passed and all four defective candidates failed.
- The additions-only critic identified `missing-exact-product-link`,
  `missing-final-theorem`, and `wrong-error-count`.
- Retrieval access was read-only, audited, and absent from stateless sessions.
- Every report and retrieval log validated.

## What failed

No retrieved-condition acceptance test failed. The condition took 57.148
seconds longer than stateless. The retrieval logs do not support attributing
the mathematical category improvement to memory, so no causal learning claim
is made.

## Reusable observations

Audited retrieval distinguishes “memory was mounted” from “memory changed a
decision.” In this run the artifacts helped enforce process/report discipline;
the observed semantic score difference still requires replication.

## Evidence

- `../comparison.json`, `../scores.json`, and `../retrieval-logs.json`
- `../frozen-manifest.json` and `../memory/`
- `../retrieved--*/evaluation/verification.json`
- `../retrieved--*/review/`

## Remaining limitations

There is one model sample per case, only one theorem family, and a ceiling on
overall verdict accuracy. The snapshot was general rather than
floating-point-specific. This shows benefit from external context in one
observed score, not learning or a change to model weights.

## Metrics

- verdicts correct: 6/6
- expected categories: 4/4
- critic wall time: 295.541 seconds
- per-case wall times: 70.74, 62.59, 38.05, 44.05, 30.07, 50.05 seconds
- compiler command events: 10
- token usage: unknown in aggregate because checkpointed runs lack final usage
- API cost: unknown
- distinct failed strategies: unknown
- Aristotle calls: 0
- final proof size: not applicable
- semantic review success: verified under the frozen retrieved-condition acceptance test
