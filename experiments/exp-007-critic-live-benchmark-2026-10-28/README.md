# Five-case live Lean critic benchmark

This critic-only experiment tests one known-complete candidate and four
compiling semantic defects. `protocol.json` preregisters the model, budget,
allowed tools, verification command, expected verdicts, and defect categories.
Expected labels are never mounted into critic containers.

Run preparation before any model call:

```bash
python3 experiments/exp-007-critic-live-benchmark-2026-10-28/prepare.py
python3 experiments/exp-007-critic-live-benchmark-2026-10-28/run_benchmark.py
```

The second command freezes all inputs, verifies every candidate, launches one
fresh isolated critic per case, and writes `scores.json`.
