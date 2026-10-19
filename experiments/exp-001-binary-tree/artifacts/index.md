# Artifact index

Experiment-local record index. Outside stateless experiments, open only relevant
entries. During a retrieved experiment, use only its approved frozen memory
snapshot; this full index is not automatically allowed input.

| Artifact ID | Status | Project | Tags | Summary | Path |
| --- | --- | --- | --- | --- | --- |
| `run-2026-10-19-floating-point-retrieved` | verified | binary-tree-reduction | retrieved, container, floating-point, critique, regression | Original theorem verified with generic memory; slower than baseline, with a protected-root write correctly blocked. | [retrieved](2026-10-19-floating-point-retrieved.md) |
| `run-2026-10-19-floating-point-stateless` | verified | binary-tree-reduction | stateless, container, floating-point, critique | Source-only fresh agent proved the original theorem without Lean hints or a worked example; independent checks passed. | [stateless](2026-10-19-floating-point-stateless.md) |
| `run-2026-10-19-capacity-retrieved` | failed | binary-tree-reduction | container, retrieved, capacity, empty submission | The service stopped before retrieval; an import-only build was correctly rejected as no proof. | [interrupted retrieved](2026-10-19-capacity-retrieved.md) |
| `run-2026-10-19-capacity-stateless` | partial | binary-tree-reduction | container, stateless, capacity | The isolated source-only attempt began but service capacity interrupted it; candidate verification failed. | [interrupted stateless](2026-10-19-capacity-stateless.md) |
| `validated-lean-binary-reduction-001` | verified | binary-tree-reduction | Lean, floating-point, tree, multiset, `Nat.clog`, induction | Reusable proof patterns from the verified Algorithm 1 construction. | [`validated/lean-binary-reduction-patterns.md`](validated/lean-binary-reduction-patterns.md) |
| `run-2026-10-11-algorithm1` | verified | binary-tree-reduction | Algorithm 1, offset pairing, carry, depth, exact sum | Exact five-input test and general preservation/depth proof. | [Algorithm 1 baseline](2026-10-11-algorithm1-offset-reduction.md) |
