# Stateless dot-product critic condition

artifact_id: `2026-10-29-dot-product-critic-stateless`
date: 2026-10-29
project: Lean critic memory ablation
status: partial
memory_mode: stateless
retrieved_artifacts: `[]`
verification: all six condition gates passed; 60 pipeline tests passed; `bash pipeline/verify.sh` passed 8,036 jobs and placeholder/custom-axiom scans.

experiment_id: `exp-012-dot-product-critic-memory-ablation-2026-10-29`
condition: stateless
task_id: `floating-point-dot-product-critic-memory-ablation`
model: `gpt-6.1-sol`
reasoning_effort: `medium`
starting_commit: `a42eeb51fa8a9ee36f5a6027bd840189198ab283`
artifact_snapshot: `frozen-manifest.json` SHA-256 `1655cbbb439ca5eee67989cfa7d43199502b49e5f7cb04e557435831ab489538`
time_limit: 240 seconds per critic
verification_command: `bash pipeline/verify.sh <condition>/evaluation-workspace`
success: false

## Request

Rerun the stateful/retrieved and stateless critic architecture on the floating-point dot-product proof.

## Target

Classify the same two complete and four compiling defective dot-product
candidates used by the retrieved condition, without external research memory.
The frozen acceptance tests required 6/6 correct verdicts, all four expected
defect categories, and no false decisions, invalid reports, or timeouts.

## Result

The condition achieved 6/6 correct verdicts with no false passes, false
rejections, invalid reports, or timeouts. It found 3/4 expected categories. On
the additions-only candidate it correctly failed the submission as
`missing-final-theorem`, but omitted the expected
`missing-exact-product-link` label. The strict condition result is partial.

## Decisions and reasoning

Every candidate passed the trusted formal gate before its fresh critic session.
The stateless containers had no `/memory` mount. Expected verdicts and defect
labels remained outside the critic containers and were applied only by the
deterministic scorer.

## What worked

- Both complete candidates passed, including the renamed theorem.
- All four defective candidates were rejected.
- The proposition-only, strengthened-assumption, and conclusion-assumed labels matched.
- Every structured report validated and no session timed out.

## What failed

The additions-only report used a valid broader completeness label but missed
the preregistered exact-product-link category. This preserves the strict miss
rather than reinterpreting it after the result.

## Reusable observations

Pass/fail accuracy and defect specificity remain separate measurements. A
critic can correctly reject a theorem while giving feedback that is too broad
to direct the most useful repair.

## Evidence

- `../comparison.json` and `../scores.json`
- `../frozen-manifest.json`
- `../stateless--*/evaluation/verification.json`
- `../stateless--*/review/`

## Remaining limitations

There is one model sample per case and only one theorem family. This condition
cannot by itself estimate critic variance or a retrieval effect.

## Metrics

- verdicts correct: 6/6
- expected categories: 3/4
- critic wall time: 238.393 seconds
- per-case wall times: 62.63, 61.64, 24.02, 32.03, 30.02, 28.04 seconds
- compiler command events: 12
- token usage: unknown in aggregate because checkpointed runs lack final usage
- API cost: unknown
- distinct failed strategies: unknown
- Aristotle calls: 0
- final proof size: not applicable
- semantic review success: partial under the frozen category-specific acceptance test
