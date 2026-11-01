# Critic benchmark infrastructure

This experiment owns the first deterministic scoring infrastructure for the
LLM Lean critic. The implementation adds optional stable requirement and defect
IDs, preserves legacy critic reports, and scores saved reports without exposing
expected labels to the critic.

No live model benchmark was run. The next step is to freeze the small set of
compiling complete and defective candidates, run fresh critics, and score their
preserved reports with `pipeline/critic_benchmark.py`.

See the [artifact index](artifacts/index.md).
