# Binary-tree theorem specification

Update this semantic checklist before changing the main Lean theorem.

## Source assumptions

- Inputs are real values `x₁, …, xₙ`.
- Each floating-point addition satisfies `fl(a+b) = (a+b)(1+δ)` with `|δ| ≤ u`.
- No overflow or underflow occurs.
- The balanced reduction depth is `L = ⌈log₂ n⌉`.
- `L*u < 1`.

## Source conclusion

```text
ŷ = Σ i, (xᵢ + Δxᵢ)
|Δxᵢ| ≤ γ_L |xᵢ|
γ_L = L*u / (1 - L*u)
```

## Lean checklist

- [ ] Represent every assumption explicitly or document why it is built into the model.
- [ ] Use arbitrary input length, not only powers of two.
- [ ] Handle unmatched nodes without unintended rounding steps.
- [ ] Preserve the exact `gamma` constant and depth bound.
- [ ] Do not add assumptions merely to make the proof easier.
- [ ] Back-translate the final Lean theorem and compare it with this specification.

## Dot-product extension

The reduction theorem treats leaves as values already available for summation. The later dot-product theorem must also model and bound rounding in each multiplication `xᵢ*yᵢ`.
