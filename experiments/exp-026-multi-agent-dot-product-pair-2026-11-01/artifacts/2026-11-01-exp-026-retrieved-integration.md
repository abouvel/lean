artifact_id: 2026-11-01-exp-026-retrieved-integration
date: 2026-11-01
project: multi-agent-dot-product-roundtrip-pilot
status: verified
memory_mode: retrieved
retrieved_artifacts: ["pilot-general-lean-001"]
verification: full candidate build/scans, elaborated axiom/protection audit, direct critic pass, round-trip pass
experiment_id: exp-026-multi-agent-dot-product-pair-2026-11-01
condition: retrieved
task_id: multi-agent-dot-product-roundtrip-pilot
model: gpt-6.1-sol
reasoning_effort: medium
starting_commit: b5df08f54d45608c2aad01a58ac3dee5ff95d8f6
artifact_snapshot: ../runs/dot-product-trial-001-retrieved/frozen-manifest.json; dirty runtime archived and hashed
time_limit: {"max_passes": 2, "builder_seconds_per_pass": 180, "critic_seconds_per_pass": 240, "revision": {"schema_version": 1, "mode": "calibration", "seconds": {"planner": 90, "formalizer": 150, "prover": 180, "translator": 180, "judge": 180}, "construction_policy": "Define rounded leaf multiplication and rounded tree reduction, then prove gamma(depth+1,u) perturbations relative to exact products. The perturbation witness may be existential; executable IEEE arithmetic is not required."}}
verification_command: bash pipeline/verify.sh
success: true

## Request

"implement this plan and work until you are able to verify it"

## Target

Define the rounded dot product and prove its full componentwise backward-error
theorem in the same abstract relative-rounding model, with the same five supplied
prerequisites and role budgets in both conditions. No locked final Lean statement
was supplied to production agents.

## Result

Accepted on pass 1. All five roles and the separate direct critic completed.
Final build/scans, transitive axiom audit, prerequisite protection, and declaration
preservation passed. Both semantic evaluators passed the exact fingerprinted candidate.

## Decisions and reasoning

Production roles communicate through explicit versioned files. Semantic evaluators
receive blinded inputs and no research memory. Logical implication alone cannot
credit an unproved final bridge. The controller requires both evaluators to agree
during calibration; uncertainty stops automatic acceptance.

## What worked

The complete frozen pipeline executed successfully with this memory condition.

## What failed

No failed pass in this run. Earlier failures remain in exp-018, exp-020, exp-021,
and exp-024; see the implementation report.

## Reusable observations

Keep mechanical proof checking and semantic correspondence separate. No lesson is
automatically promoted; controlled tests do not establish universal evaluator accuracy.

## Evidence

[Implementation report](../REPORT.md), [comparison](../comparison.json),
[full structured run record](../runs/dot-product-trial-001-retrieved/artifacts/2026-11-01-retrieved.json).

## Remaining limitations

Expert semantic adjudication is pending. This single stateless-first pair does
not establish a memory advantage. Generic memory was opened in the retrieved
condition but no decisions were recorded as influenced. Costs remain unknown.

## Metrics

Proof-loop wall seconds: 404.828.
Total model-session seconds: 328.767.
Model sessions: 6. Aristotle calls: 0.
Token measurements are preserved in the structured record. Distinct failed
mathematical strategies and isolated final proof size: unknown.
