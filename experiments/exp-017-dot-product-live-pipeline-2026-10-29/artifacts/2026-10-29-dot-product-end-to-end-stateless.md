# Dot-product end-to-end proof run: stateless

artifact_id: `2026-10-29-dot-product-end-to-end-stateless`
date: 2026-10-29
project: floating-point-dot-product-backward-error
status: verified
memory_mode: stateless
retrieved_artifacts: []
verification: job-specific trusted gate and independent critic passed; 72 pipeline tests and repository-wide `bash pipeline/verify.sh` passed (8,036 jobs, no placeholders/custom axioms).

experiment_id: `exp-017-dot-product-live-pipeline-2026-10-29`
condition: stateless
task_id: `floating-point-dot-product-backward-error`
model: `gpt-6.1-sol`
reasoning_effort: `medium`
starting_commit: `a42eeb51fa8a9ee36f5a6027bd840189198ab283`
artifact_snapshot: batch-manifest.json SHA-256 `04db7773c16173e6409704879d1e8f99121ca280f5bbad4122e134e423f606fb`
time_limit: 2 passes, 180 builder seconds/pass, 240 critic seconds/pass, 2,400 whole-job seconds
verification_command: `bash pipeline/verify.sh`
success: true

## Request

ok can you test this out with just the one proof from earlier

## Target

Build the floating-point dot-product backward-error theorem from the natural-language specification and five prerequisite Lean modules. Prove that rounded multiplication followed by rounded tree addition equals the exact sum of leafwise perturbations of exact products, with bound gamma(depth+1,u), for arbitrary models and trees under only the requested smallness condition.

## Result

Accepted on the first pass. The trusted build and placeholder/custom-axiom scans passed. The independent critic passed all six catalog requirements with no extra assumptions or missing obligations.

## Decisions and reasoning

Both jobs began with the same `import Mathlib` submission and five identical prerequisite modules; no completed dot-product proof, prior candidate, prior report, or other condition's output was mounted. Source comparison after completion confirmed the five supplied modules were unchanged. The jobs ran with the same model, reasoning effort, tools, and budgets, stateless first.

The builder received no memory mount. It composed a multiplication perturbation lemma with the supplied rounded-sum perturbation theorem, then used the gamma step inequality.

## What worked

The actual queue, archived coordinator and worker, preflight, resource leases, builder, verifier, critic, result validation, SQLite collection, and full-text search completed. No repair pass was needed.

## What failed

No acceptance gate failed in this fresh experiment. Earlier experiment exp-016 stopped after its accepted stateless job because a generated artifact index had mistakenly been frozen as input. That evidence is preserved. The planner now excludes job-local generated artifacts, and a regression test covers their mutation.

## Reusable observations

The two proof strategies both succeeded under equal budgets. One successful pair is an end-to-end functionality test; it cannot establish a general retrieval advantage. The retrieved proof loop took longer in this run.

## Evidence

- [Collected result](../runs/dot-product-trial-001-stateless/collected-result.json)
- [Proof](../runs/dot-product-trial-001-stateless/stateless/passes/pass-001/stateless/workspace/Research/Submission.lean)
- [Verification](../runs/dot-product-trial-001-stateless/stateless/passes/pass-001/stateless/evaluation/verification.json)
- [Critic](../runs/dot-product-trial-001-stateless/stateless/passes/pass-001/stateless/review/review.json)
- [Comparison](../comparison.json)

## Remaining limitations

One theorem and one successful pair were measured. Five proved prerequisites were supplied, so this is not a from-scratch formalization of all floating-point theory. The natural-language target was authoritative; the PDF was present only for launcher compatibility. API cost is unavailable. No human semantic sign-off or causal retrieval benefit is claimed.

## Metrics

- passes used: 1
- proof-loop wall time: 151.471 seconds (excludes preflight, connectivity, queue wait, and cleanup)
- builder time: 59.939 seconds
- critic time: 63.946 seconds
- builder compiler-command events: 3
- new submission lines: 66
- source lines including prerequisites: 760
- builder tokens: {"input_tokens": 196193, "cached_input_tokens": 169344, "output_tokens": 1633, "reasoning_output_tokens": 99}
- critic tokens: {"input_tokens": 160875, "cached_input_tokens": 126720, "output_tokens": 1849, "reasoning_output_tokens": 248}
- API cost: unknown
- distinct failed strategies: unknown
- Aristotle calls: 0
- semantic review passed: true
