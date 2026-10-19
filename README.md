# Lean Numerical Analysis Research

Lean 4 numerical-analysis proofs and controlled agent experiments.

## Current work

- **Dot-product pilot:** an exact-real theorem used to test Lean and Aristotle integration.
- **Binary-tree reduction:** algorithm preservation, logarithmic depth, and deterministic backward-error bounds under an abstract relative-error model. This is not an IEEE 754 bit-level verification.
- **Agent pilot:** isolated stateless/retrieved builders, fresh offline verification, and independent critics. Both passed; retrieved was 17.2% slower in this single pair. No learning or cost-saving conclusion follows.

## Repository layout

```text
Research/                       Proof code: Common/ and Projects/
projects/                       Human-facing mathematical plans and explanations
pipeline/                       Executable machinery: build, isolate, run, verify
experiments/                    Evidence: frozen inputs, submissions, logs, metrics
artifacts/                      Searchable memory: concise run summaries and lessons
output/slides/                  Presentation deliverables
```

## Build

```bash
lake exe cache get
bash pipeline/verify.sh
```

The project is pinned to Lean and Mathlib `v4.28.0` for Aristotle compatibility.

## Why the root files stay

| File | Purpose |
| --- | --- |
| `Research.lean` | Library entry point: imports the research modules to build. |
| `lakefile.toml` | Build configuration and declared dependencies. |
| `lake-manifest.json` | Lockfile: exact resolved dependency commits. |
| `lean-toolchain` | Exact Lean compiler version. |

These are complementary, not duplicate files. Keep them at the root.

## Reproduce the agent pilot

From WSL at the repository root:

```bash
# Check frozen inputs and display the recorded results; no model call.
python3 pipeline/experiment.py check

# Rebuild both saved submissions in fresh offline containers; no model call.
python3 pipeline/experiment.py replay --run-id replay-001

# Fresh agents, same frozen task and generic memory; uses model quota.
python3 pipeline/experiment.py run --run-id pair-002
```

See [the reproduction guide](pipeline/REPRODUCE.md) for prerequisites and image builds,
and [the completed report](experiments/memory-ablation/2026-10-19-binary-tree-pilot-gpt61/REPORT.md)
for the original results. New runs never overwrite that evidence. Reproduction
means repeating the protocol, not guaranteeing identical model outputs.

## What goes where

`pipeline/` is the machinery; `experiments/` is what happened when it ran;
`artifacts/` is what a future agent may retrieve. An artifact links to experiment
evidence rather than copying its transcript. `projects/` explains the mathematics;
new execution logs belong in `experiments/`, not a second project run directory.

## Proving policy

1. Fix and review the Lean statement before proof generation.
2. Break the proof into small lemmas.
3. Try Mathlib search, inexpensive tactics, and compiler-guided repair first.
4. Use Aristotle only for a small blocked lemma.
5. Accept a result only after local Lean verification and a semantic comparison with the source theorem.

See [`projects/binary-tree-reduction/README.md`](projects/binary-tree-reduction/README.md) for the active project and [`pipeline/README.md`](pipeline/README.md) for the workflow.
