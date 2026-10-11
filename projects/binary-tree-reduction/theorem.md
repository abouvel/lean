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

- [x] Represent every assumption explicitly or document why it is built into the model.
- [x] Use arbitrary nonempty input length, not only powers of two.
- [x] Handle shorter leaf paths without unintended rounding steps in the general tree theorem.
- [x] Preserve the exact `gamma` constant and depth bound.
- [x] Do not add assumptions merely to make the proof easier.
- [x] Back-translate the final Lean theorem and compare it with this specification.

## Dot-product extension

The reduction theorem treats leaves as values already available for summation. The later dot-product theorem must also model and bound rounding in each multiplication `xᵢ*yᵢ`.

The current deterministic dot-product theorem accounts for one rounded
multiplication plus at most `tree.depth` rounded additions. The source's
probabilistic dot-product result is a separate extension and is not yet claimed.
