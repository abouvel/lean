# Experiment evidence

Each experiment owns its config, frozen inputs/memory, candidates, reviews,
metrics, notes, presentations, and artifact summaries. Shared code and Docker
files live in `../pipeline/`; the proof library lives in `../lean/`.
Each experiment's `artifacts/index.md` indexes its lessons and runs.

- [Experiment 1: binary-tree formalization](exp-001-binary-tree/README.md)
  includes the completed pair and its separate `interrupted/` attempts.
- [Experiment 2: bounded builder/critic comparison](exp-002-bounded-2026-10-23/README.md):
  both partial candidates compiled; both critics timed out. No accepted solution or memory benefit established.
- `dot_product/`: original Lean/Aristotle integration pilot; historical evidence.

See [reproduction commands](../pipeline/REPRODUCE.md). New runs use new IDs.
Old workspace/config copies are evidence, not additional projects to maintain.
Historical IDs and manifests are preserved; `relocation.json` maps moved paths.
