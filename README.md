# Lean numerical-analysis research

```text
lean/           Reusable, checked Lean proof library
pipeline/       Shared agent runner, verifier, and Docker setup
experiments/    Each experiment's inputs, notes, proofs, results, lessons, slides
```

Start with [Experiment 1: binary-tree reduction](experiments/exp-001-binary-tree/README.md).
Its [report](experiments/exp-001-binary-tree/REPORT.md) records both conditions:
both passed; retrieved was 17.2% slower in this single pair. No learning or
cost-saving benefit is established.

## Verify the proof library

```bash
lake exe cache get
bash pipeline/verify.sh
```

Lean and Mathlib are pinned to `v4.28.0`. The library lives in
[`lean/Research/`](lean/Research); `Research` is its Lean module name, not a
separate project. `lakefile.toml` selects the source directory;
`lake-manifest.json` locks dependencies; `lean-toolchain` pins the compiler.

## Inspect / reproduce Experiment 1

```bash
cd experiments/exp-001-binary-tree
python3 ../../pipeline/run.py check --config experiment.json
```

See the [pipeline](pipeline/README.md) and [reproduction commands](pipeline/REPRODUCE.md)
for offline replay and fresh agents. Experiment-local `artifacts/index.md` files
index lessons and run summaries; `memory/` is the separately frozen retrieval
snapshot. There are no separate root-level project or artifact stores.
