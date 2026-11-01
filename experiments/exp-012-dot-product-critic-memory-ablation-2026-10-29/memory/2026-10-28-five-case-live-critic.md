# Five-case live critic benchmark

```text
artifact_id: 2026-10-28-five-case-live-critic
date: 2026-10-28
project: lean-critic-five-case-smoke-benchmark
status: partial
memory_mode: stateless
retrieved_artifacts: []
verification: all five case gates passed; bash pipeline/verify.sh — passed after the run

experiment_id: exp-009-critic-live-benchmark-2026-10-28
condition: stateless
task_id: lean-critic-five-case-smoke-benchmark
model: gpt-6.1-sol
reasoning_effort: medium
starting_commit: a42eeb51fa8a9ee36f5a6027bd840189198ab283
artifact_snapshot: sha256:9f883f4496a25fcd092d785cf87e4afa253ab752d74d35cfae9e14a26f17f630
time_limit: 240 seconds per critic
verification_command: bash pipeline/verify.sh <case>/evaluation-workspace
success: false
```

## Request

Test the improved LLM critic agent on a small reusable benchmark.

## Target

Preserve the preregistered acceptance tests:

1. Every candidate passes Lean compilation and placeholder/custom-axiom scans.
2. The correct candidate receives a valid pass.
3. Every defective candidate receives a valid fail with its preregistered defect category.
4. No report is malformed and no critic times out.

## Result

All five overall verdicts were correct. There were no false passes, false
rejections, invalid reports, or timeouts. Three of four expected defect
categories were found. The concrete-example candidate was correctly rejected
as `missing-final-theorem`, but the preregistered specific category was
`concrete-example-only`. Because acceptance test 3 required the expected
category, the strict experiment result is partial rather than verified success.

## Decisions and reasoning

Expected labels were written before critic launch and were never mounted into
reviewer containers. Each case used a fresh critic session with the same model,
reasoning effort, tools, source, rubric, catalog, time limit, and verification
procedure. The complete candidate and two historical incomplete candidates were
frozen; two additional defects were deterministic source transformations.

The category miss was preserved rather than reinterpreted after observing the
report. `concrete-example-only` and `missing-final-theorem` overlap conceptually,
so a future taxonomy should represent parent/child or multi-label relations.

## What worked

- Five of five candidates passed the formal gate before critic launch.
- The known-complete proof passed semantic review.
- All four defective proofs were rejected.
- The original-input linkage, proposition-only, and assumed-conclusion defects
  received their preregistered categories.
- Early checkpoints reduced defective-case review time to 22.041–32.042 seconds.
- All structured reports validated against the stable-ID catalog.

## What failed

The concrete-example defect received the broader `missing-final-theorem`
category instead of `concrete-example-only`. This is either a critic specificity
error or evidence that the flat taxonomy does not represent overlapping defects
well; the completed benchmark score records it as a miss.

Two earlier experiment IDs failed during setup before any model call: exp-007
started an unintended local dependency rebuild and was interrupted; exp-008
froze but failed container workspace permissions. Both are preserved and are
excluded from the live score.

## Reusable observations

- Overall pass/fail accuracy and defect-category specificity are distinct.
- A flat single-level defect taxonomy makes overlapping categories ambiguous.
- Completeness checkpoints were substantially cheaper than the complete review
  in this small run.
- A passing formal gate did not hide any of the four semantic defects from the
  critic.

## Evidence

- [Preregistered protocol](../protocol.json)
- [Frozen manifest](../frozen-manifest.json)
- [Deterministic scores](../scores.json)
- [Readable report](../REPORT.md)
- Per-case candidates, formal verification logs, critic events, metrics, and
  reports remain in each case directory.

## Remaining limitations

- Only five cases and one model sample per case were run.
- Three defective cases are easy completeness failures; this does not measure
  subtle proof-level semantic auditing broadly.
- The complete and historical candidates come from the same theorem family.
- Token usage for checkpoint-stopped critics is unavailable; cost is unknown.
- No held-out theorem family or model comparison was run.

## Metrics

| Metric | Value |
| --- | ---: |
| Overall verdicts correct | 5/5 |
| Expected defect categories found | 3/4 |
| False passes | 0 |
| False rejections | 0 |
| Invalid reports | 0 |
| Timeouts | 0 |
| Aggregate critic time | 192.446 s |
| Complete-case input tokens | 158,882 |
| Complete-case cached input subset | 128,896 |
| Complete-case output tokens | 2,934 |
| Other token usage | unknown |
| Monetary cost | unknown |
| Aristotle calls | 0 |
