# Lean Numerical Analysis Research

This repository contains Lean 4 formalizations for numerical-analysis research and a small, reproducible proving pipeline.

## Current work

- **Dot-product pilot:** an exact-real theorem used to test Lean and Aristotle integration.
- **Binary-tree reduction:** the active project, targeting a floating-point backward-error proof and a later dot-product extension.

## Repository layout

```text
Research/Common/                 Reusable Lean definitions and lemmas
Research/Projects/               Project-specific Lean formalizations
projects/                        Project plans, source statements, and run records
pipeline/                        Shared verification and submission workflow
experiments/dot_product/         Original dot-product pilot record
```

## Build

```bash
lake exe cache get
lake build
```

The project is pinned to Lean and Mathlib `v4.28.0` for Aristotle compatibility.

## Proving policy

1. Fix and review the Lean statement before proof generation.
2. Break the proof into small lemmas.
3. Try Mathlib search, inexpensive tactics, and compiler-guided repair first.
4. Use Aristotle only for a small blocked lemma.
5. Accept a result only after local Lean verification and a semantic comparison with the source theorem.

See [`projects/binary-tree-reduction/README.md`](projects/binary-tree-reduction/README.md) for the active project and [`pipeline/README.md`](pipeline/README.md) for the workflow.
