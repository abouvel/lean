# Dot-product critic benchmark

artifact_id: `exp-011-dot-product-critic-benchmark`
date: 2026-10-29
project: Lean critic
status: verified
memory_mode: stateless
retrieved_artifacts: `[]`
verification: `python3 -m unittest discover -s pipeline/tests -p 'test_*.py'` passed 58 tests; `bash pipeline/verify.sh` passed an 8,036-job build and placeholder/custom-axiom scans.

experiment_id: `exp-011-dot-product-critic-2026-10-28`
condition: stateless
task_id: `floating-point-dot-product-critic-benchmark`
model: `gpt-6.1-sol`
reasoning_effort: `medium`
starting_commit: `a42eeb51fa8a9ee36f5a6027bd840189198ab283`
artifact_snapshot: `frozen-manifest.json` SHA-256 `6df3632c3ab8613565b2ebd36c5cb802e0dbd4571e843d881cf9da91561b70bb`
time_limit: 240 seconds per critic
verification_command: `bash pipeline/verify.sh <case>/evaluation-workspace`
success: true

## Request

Test the entire critic architecture on the floating-point dot-product proof.

## Target

Audit the full `roundedDotProduct_exists_perturbation` theorem: rounded leaf
multiplication plus rounded tree reduction must equal the exact sum of
leafwise perturbations of exact products, bounded by
`gamma (tree.depth + 1) model.u`, without strengthening assumptions.

Acceptance tests were frozen before critic launch:

1. Every case passes the trusted Lean gate.
2. Both correct candidates receive valid passes.
3. Every defective candidate receives a valid fail containing its expected defect category.
4. There are no false passes, false rejections, invalid reports, or timeouts.

## Result

All acceptance tests passed. The deterministic scorer recorded 6/6 correct
verdicts and 4/4 expected defect categories, with zero false passes, false
rejections, invalid reports, or timeouts.

## Decisions and reasoning

The benchmark used two correct proofs (original and declaration-renamed) and
four compiling defects (proposition-only, additions-only, zero-unit-roundoff,
and conclusion-assumed). Every candidate first passed the same trusted Lean
build and scans. Each then received a fresh isolated LLM critic. Hidden labels
were consulted only by the deterministic scorer.

Stable requirement and defect IDs were supplied in `evaluator/requirements.json`.
The run was resumed from its unchanged frozen manifest after removing only
Docker-generated `.lake/build` caches that an earlier preflight left
root-owned; frozen hashes were rechecked before any critic call.

## What worked

- Both complete proofs passed, including the renamed theorem.
- All four semantic defects were rejected at the completeness checkpoint.
- The subtle additions-only proof was correctly identified as lacking the link to exact products.
- The critic detected both an extra exact-arithmetic assumption and a conclusion copied into the hypotheses.
- Structured report validation and deterministic scoring accepted all six outputs.

## What failed

The first frozen invocation stopped before any critic call because preflight
Docker caches were root-owned and the runner attempted to chmod them. Removing
only those disposable caches and rechecking frozen hashes allowed the same
frozen run to resume. Earlier setup-only experiment `exp-010` preserves its
infrastructure failure rather than treating it as a model result.

## Reusable observations

- A separate formal gate is necessary but insufficient: all four defective candidates compiled and passed placeholder/custom-axiom scans.
- An early completeness checkpoint makes obvious semantic failures faster and keeps reports focused.
- Stable defect IDs enable deterministic scoring while still allowing the critic to report additional defensible defects.
- Reviewer workspaces should discard or normalize container-owned build caches before repeated host-side ownership checks.

## Evidence

- `scores.json`: case-level deterministic scores.
- `frozen-manifest.json`: frozen configuration and input hashes.
- `benchmark.json`: hidden expected verdict/category manifest consumed by the scorer.
- `<case>/evaluation/verification.json`: trusted gate result for every candidate.
- `<case>/review/`: structured critic output, event log, and metrics.
- `REPORT.md`: concise result and architecture summary.

## Remaining limitations

This benchmark has only six hand-constructed cases from one theorem family. It
does not measure performance on natural historical failures or model-generated
wrong-but-compiling mutations. Extra defect labels were not penalized. Aggregate
token usage is unavailable because checkpointed runs report token usage as
unknown.

## Metrics

- critic wall-clock time: 317.111 seconds total
- per-case critic times: 71.235, 119.705, 34.043, 30.042, 32.044, 30.042 seconds
- token usage: unknown in aggregate; available for the two full reviews only
- API cost: unknown
- compiler command events: 8
- distinct failed strategies: unknown
- Aristotle calls: 0
- final proof size: not applicable (critic-only benchmark)
- formal-gate success: 6/6
- semantic-review success: 6/6 correct verdicts; 4/4 expected defects found
