# Experiment 1 — binary-tree floating-point proof

**Question:** Do frozen proof-engineering notes improve source-to-Lean formalization?

| | Stateless | Retrieved |
| --- | --- | --- |
| Input | Paper + clean Lean project | Same + frozen generic notes |
| Builder time | 458.993 s | 538.043 s |
| Offline Lean verification | Pass | Pass |
| Independent critic | Pass | Pass |
| Aristotle calls | 0 | 0 |

Retrieved was **17.2% slower** in this single pair. No learning or savings benefit
is established. The supplied paper includes its mathematical proof; neither
builder received an existing Lean solution, worked example, or prior chat.

```text
exp-001-binary-tree/
├── experiment.json       Model, limits, conditions, input paths
├── inputs/               Original paper, text, builder assignment
├── evaluator/            Protected Lean scaffold, verifier, critic rubric
├── memory/               Frozen notes for retrieved only
├── stateless/            Candidate, transcript, verification, critic
├── retrieved/            Candidate, transcript, verification, critic
├── artifacts/            Searchable summaries of both pairs
├── interrupted/          Earlier capacity-interrupted pair; kept separate
├── REPORT.md             Detailed findings and evidence links
├── comparison.json       Recorded metrics and judgments
├── frozen-manifest.json  Original settings/hashes, unchanged
└── relocation.json       Historical path mapping and provenance
```

## Run from here

```bash
python3 ../../pipeline/run.py check --config experiment.json
python3 ../../pipeline/run.py replay --config experiment.json --name replay-001
python3 ../../pipeline/run.py run --config experiment.json --name exp-002-binary-tree
```

Only `run` calls models. Replay and fresh runs create new sibling experiment
folders; this evidence is never overwritten. [Setup](../../pipeline/REPRODUCE.md).

## Open results

- [Full report](REPORT.md) · [comparison](comparison.json)
- Stateless: [proof](stateless/workspace/Research/Submission.lean) · [critic](stateless/review/review.md)
- Retrieved: [proof](retrieved/workspace/Research/FloatingPoint.lean) · [critic](retrieved/review/review.md)
- [Stateless summary](artifacts/2026-10-19-floating-point-stateless.md) · [retrieved summary](artifacts/2026-10-19-floating-point-retrieved.md)

Historical records retain the original experiment ID `2026-10-19-binary-tree-pilot-gpt61`.
Relocation changes navigation, not the reported measurements. The shared
[pipeline](../../pipeline/README.md) is outside this folder; no task-specific prompt is embedded in it.
