# Floating-point formalization with a frozen generic memory snapshot

```text
artifact_id: run-2026-10-19-floating-point-retrieved
date: 2026-10-19
project: binary-tree-reduction
status: verified
memory_mode: retrieved
retrieved_artifacts: pilot-general-lean-001
verification: full trusted offline build/scans passed; independent critic and compiled acceptance checks passed
experiment_id: 2026-10-19-binary-tree-pilot-gpt61
condition: retrieved
task_id: sahil-theorem-3.1-algorithm-1
model: gpt-6.1-sol
reasoning_effort: medium
starting_commit: 66a6e9e85488743ca7f8adad84260103bcaddaa0
artifact_snapshot: experiment memory/ and frozen-manifest.json; read-only, with file hashes and source provenance
time_limit: 1200 seconds
verification_command: bash pipeline/verify.sh
success: true
```

## Request

> wait. the first run doesn't recieve any lean instructions. can you execute this plan

## Target

Same source, task, import-only starting project, model, effort, tools, and budget
as the stateless condition. Additionally permit a frozen snapshot of generic
Lean notes. Exclude the worked example, target answer, prior project code, and
earlier conversation.

## Result

Completed a 549-line, three-module formalization. It implements the original
indexed reduction with actual addition operations, proves equivalence to an
error-labelled tree, and establishes the general gamma backward-error theorem.
Trusted offline verification and separate critic checks passed. It took 17.2%
longer and used more tokens than the baseline in this single pair.

## Decisions and reasoning

The actor used error-labelled nodes and a scalar error recurrence, then added
an indexed arithmetic execution and proved its equivalence. The principal
theorem assumes the relative-error model only on executed additions. Carries
return the previous subtree/value unchanged.

Artifact access: file enumeration included `/memory`; the actor read
`/memory/index.md`, then `/memory/general-lean.md`. The exact commands are in
the JSONL transcript. The retrieval log identifies `pilot-general-lean-001` and
reports using `abs_add_le`, denominator positivity, and import-build advice.
The proof uses the first two patterns; this does not establish a causal benefit,
and no retrieval-help claim is made.

## What worked

The frozen snapshot was available only to this actor and was actually opened.
The final formalization and independent checks cover the hidden five-input
trace, duplicates/singletons, composite-subtree carries, and nonzero rounding
errors. Audited axiom dependencies were standard foundations only.

## What failed

Initial list API names, induction/indexing, nonnegative arithmetic, and a
dependent import needed repair. An attempted rewrite of protected
`Research.lean` was blocked by the read-only mount. The actor subsequently used
the permitted `Research/Submission.lean` import wrapper. No protected change
succeeded. This is a boundary interaction, not evidence of malicious intent.

## Reusable observations

Correct final code and process compliance are separate. Read-only guards can
block a protected action even when an agent attempts it. A process critic needs
the sanitized action trace, not just the final code. Retrieval can occur without
observed efficiency improvement. No shared validated lesson is promoted here.

## Evidence

- [Experiment report](../../experiments/memory-ablation/2026-10-19-binary-tree-pilot-gpt61/REPORT.md)
- [Main theorem](../../experiments/memory-ablation/2026-10-19-binary-tree-pilot-gpt61/retrieved/workspace/Research/FloatingPoint.lean)
- [Tree proof](../../experiments/memory-ablation/2026-10-19-binary-tree-pilot-gpt61/retrieved/workspace/Research/BinaryTree.lean)
- [Exact prompt](../../experiments/memory-ablation/2026-10-19-binary-tree-pilot-gpt61/retrieved/output/actual-prompt.txt)
- [Retrieval log](../../experiments/memory-ablation/2026-10-19-binary-tree-pilot-gpt61/retrieved/output/retrieval.md)
- [Decisions](../../experiments/memory-ablation/2026-10-19-binary-tree-pilot-gpt61/retrieved/output/decisions.md)
- [Critic](../../experiments/memory-ablation/2026-10-19-binary-tree-pilot-gpt61/retrieved/review/review.json)

## Remaining limitations

One source-assisted same-assignment pilot with manually curated generic memory,
not held-out transfer or autonomous memory construction. Fixed order, shared
machine, provider caching, and model variation limit inference. No model-weight
learning, dollar-savings claim, critic-accuracy estimate, or jailbreak-resistance
benchmark. Abstract deterministic arithmetic model, not IEEE or probability.

## Metrics

```text
wall_time_seconds: 538.043
input_tokens: 1660099
cached_input_tokens: 1591040
output_tokens: 25039
reasoning_output_tokens: 9286
cost: unknown
compiler_command_events: 27
distinct_failed_strategies: unknown
aristotle_calls: 0
submitted_source_lines: 549
offline_verification_seconds: 23.325
critic_seconds: 132.397
semantic_review: independent critic pass; human sign-off not claimed
protected_root_write_attempt: blocked; no mutation succeeded
```
