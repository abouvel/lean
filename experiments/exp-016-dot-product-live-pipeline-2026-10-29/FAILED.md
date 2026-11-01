# Interrupted paired run: mutable artifact index frozen as input

The stateless builder completed its first proof pass, passed trusted Lean
verification and independent criticism, and was collected as accepted. Before
launching the retrieved job, the coordinator's frozen-input guard rejected the
stateless job's newly written `artifacts/index.md`.

The batch planner had incorrectly included that generated output index among
immutable files. The run is partial and is preserved without modifying its
frozen implementation or relabeling its successful stateless proof. The
retrieved job was not launched. A regression check and an exclusion of the
job-local generated `artifacts/` directory were added before a fresh paired run.
