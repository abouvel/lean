# Binary-tree floating-point reduction

## Objective

Formalize the backward-error analysis of floating-point binary-tree summation, then extend it to a floating-point dot product.

The model starts from

```text
fl(a + b) = (a + b)(1 + δ),  |δ| ≤ u.
```

For a balanced reduction of `n` inputs, let `L = ⌈log₂ n⌉`. Under the no-overflow, no-underflow, and `L*u < 1` assumptions, the target is

```text
ŷ = Σ i, (xᵢ + Δxᵢ),  |Δxᵢ| ≤ γ_L |xᵢ|,
γ_L = L*u / (1 - L*u).
```

## Proof order

1. Define the abstract rounding model.
2. Define `gamma` and prove the accumulated product-error bound.
3. Define exact and rounded binary-tree evaluation.
4. Prove that each leaf accumulates at most one error per tree level.
5. Build a balanced tree for arbitrary `n` and prove its depth bound.
6. Prove the binary-tree backward-error theorem.
7. Add rounded multiplication and derive the dot-product theorem.

## Scope

- Start with the relative-error model, not bit-level IEEE 754.
- A power-of-two result may be intermediate; the final result supports general `n`.
- The full dot product includes multiplication and reduction error.
- A Lean build is required, but the statement must also match the source theorem.

## Status

- [x] Repository and module structure
- [x] Abstract model scaffold
- [x] `gamma` definition
- [x] Tree and rounded-evaluation definitions
- [x] Product-of-rounding-errors bound
- [x] Backward-error theorem for an arbitrary tree of bounded depth
- [x] Four-input verification example
- [x] Deterministic dot-product theorem for an arbitrary tree
- [x] Algorithm 1 offset-paired construction for every nonempty input list
- [x] Input-multiset preservation and unmatched-element carry theorem
- [x] Depth bound `≤ Nat.clog 2 n = ⌈log₂ n⌉`
- [x] Specialize the backward-error theorem to Algorithm 1
- [ ] Connect the deterministic result to the probabilistic theorem, if required

See [`theorem.md`](theorem.md) for the source-to-Lean checklist.
