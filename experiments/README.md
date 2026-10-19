# Experiment evidence

Each experiment owns its config, frozen inputs/memory, candidates, reviews,
metrics, and artifact summaries. Shared code and Docker files live in `../pipeline/`.
The global artifact index links here instead of duplicating run records.

- [Experiment 1: binary-tree formalization](exp-001-binary-tree/README.md)
  includes the completed pair and its separate `interrupted/` attempts.
- `dot_product/`: original Lean/Aristotle integration pilot; historical evidence.

See [reproduction commands](../pipeline/REPRODUCE.md). New runs use new IDs.
Old workspace/config copies are evidence, not additional projects to maintain.
Historical IDs and manifests are preserved; `relocation.json` maps moved paths.
