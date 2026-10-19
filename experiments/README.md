# Experiment evidence

Each experiment owns its frozen inputs, candidate sources, logs, and results.
The runner lives in `../pipeline/`; searchable summaries live in `../artifacts/`.
Do not copy full logs into either directory.

- [Completed container pilot](memory-ablation/2026-10-19-binary-tree-pilot-gpt61/REPORT.md)
- `memory-ablation/2026-10-19-binary-tree-pilot/`: earlier capacity-interrupted pair; retained, not pooled with the completed pair.
- `dot_product/`: original Lean/Aristotle integration pilot; historical evidence.

See [reproduction commands](../pipeline/REPRODUCE.md). New runs use new IDs.
Old workspace/config copies are run snapshots, not additional source projects
to maintain. Keep them intact while their manifests and reports reference them.
