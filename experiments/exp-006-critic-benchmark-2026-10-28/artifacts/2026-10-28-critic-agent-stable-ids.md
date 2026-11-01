# Stable-ID critic contract and benchmark scorer

```text
artifact_id: 2026-10-28-critic-agent-stable-ids
date: 2026-10-28
project: critic-agent-benchmark-infrastructure
status: verified
memory_mode: retrieved
retrieved_artifacts: [2026-10-27-critic-contract-canary]
verification: python3 -m unittest discover -s pipeline/tests -p 'test_*.py' — 58 passed; bash pipeline/verify.sh — passed (8,036 jobs; placeholder/custom-axiom scans passed)

experiment_id: exp-006-critic-benchmark-2026-10-28
condition: retrieved
task_id: improve-lean-critic-agent
model: unknown
reasoning_effort: unknown
starting_commit: a42eeb51fa8a9ee36f5a6027bd840189198ab283
artifact_snapshot: not applicable; infrastructure implementation on an existing dirty worktree
time_limit: unknown
verification_command: bash pipeline/verify.sh
success: true
```

## Request

Build or improve the critic agent using the agreed minimum architecture: keep
the LLM semantic critic, test it with compiling candidates that contain known
semantic defects, and avoid building a sophisticated mutation system.

## Target

Add stable requirement and defect-category IDs to new critic runs, validate the
structured reports deterministically, score saved reports against hidden labels,
and preserve the existing production checkpoint flow and historical reports.

## Result

The critic can now receive an optional task-specific `requirements.json`. When
present, final reports must cover every catalog requirement exactly once, use
only allowed defect IDs, and classify every failed requirement. Completeness
checkpoints may remain partial so obvious defects can return quickly to a
builder. Experiments without a catalog keep the legacy contract.

`pipeline/critic_benchmark.py` scores preserved reports after the critic exits.
It separates verdict accuracy, expected-defect detection, false passes, false
rejections, invalid reports, and timeouts. Templates and unit tests cover the
catalog and scoring contracts.

## Decisions and reasoning

The retrieved canary artifact showed that launch, checkpoint, timeout, and JSON
routing already worked on one complete and one incomplete candidate. That
evidence changed the implementation decision: this run did not rebuild the
orchestrator and instead added the missing measurement layer for critic judgment.

Requirement catalogs are optional so frozen historical experiments remain
readable. Hidden expected verdicts belong only to the post-run scorer and are
never staged by the critic launcher. Repair feedback retains both the stable ID
and human-readable requirement text.

## What worked

- Focused critic tests passed: 26 tests.
- Full pipeline unit suite passed: 58 tests.
- The full repository verification gate passed: 8,036 build jobs plus the
  placeholder and custom-axiom scans.
- Existing unrelated dirty-worktree changes and experiment evidence were
  preserved.

## What failed

The Windows patch helper rejected direct edits through the WSL UNC reparse
point. Changes were staged in the authorized local workspace, diffed, and
applied to the same checkout. This affected editing mechanics, not the code or
verification result.

No live LLM critic cases were run, so this artifact contains no critic-accuracy
result.

## Reusable observations

- Report-contract reliability and semantic judgment accuracy should be measured
  separately.
- Stable IDs make deterministic scoring possible without locking the Lean
  theorem statement.
- Early completeness checkpoints remain useful in production, while a later
  full-report benchmark can measure requirement recall.

## Evidence

- `pipeline/critic.py`: optional catalog staging, prompting, and validation.
- `pipeline/critic_benchmark.py`: deterministic hidden-label scorer.
- `pipeline/tests/test_critic.py` and `test_critic_benchmark.py`: contract and
  scoring tests.
- `pipeline/examples/critic-requirements.json` and
  `critic-benchmark.json`: starting templates.
- `pipeline/README.md`: usage and trust-boundary documentation.

## Remaining limitations

- The proposed 4–6 compiling benchmark variants have not yet been frozen or
  sent to live critics.
- There is no evidence yet that the LLM critic detects the cataloged defects
  reliably on unseen candidates.
- Repeated runs, held-out theorem families, and model-version comparisons remain
  future work.

## Metrics

| Metric | Value |
| --- | ---: |
| Focused critic tests | 26 passed |
| Full pipeline tests | 58 passed |
| Lean verification jobs | 8,036 |
| Live critic calls | 0 |
| Compiler attempts | unknown |
| Wall-clock time | unknown |
| Token usage | unknown |
| Monetary cost | unknown |
| Aristotle calls | 0 |
