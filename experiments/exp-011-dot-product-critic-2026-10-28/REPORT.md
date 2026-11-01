# Floating-point dot-product critic benchmark report

The complete critic pipeline succeeded on all six frozen, compiling candidates.

## Result

| Metric | Result |
| --- | ---: |
| Verdicts correct | 6 / 6 |
| Expected defect categories found | 4 / 4 |
| False passes | 0 |
| False rejections | 0 |
| Invalid reports | 0 |
| Timeouts | 0 |

The two complete proofs passed. The critic rejected all four semantic defects:

- a proposition stated but not proved;
- an additions-only theorem linked to already-rounded products;
- a theorem restricted by `model.u = 0`;
- a theorem that assumed its own conclusion.

The additions-only critic also reported `missing-final-theorem` and
`wrong-error-count`; the zero-unit-roundoff critic also reported
`weakened-quantification`; and the conclusion-assumed critic also reported
`missing-final-theorem` and `strengthened-assumption`. These extra labels are
consistent with the candidates and did not affect the preregistered scoring.

## Architecture exercised

```text
frozen compiling candidate
          |
          v
trusted Lean build + placeholder/custom-axiom scans
          |
          v
fresh isolated LLM critic (gpt-6.1-sol, medium)
          |
          v
schema/catalog validation
          |
          v
hidden deterministic verdict + defect scoring
```

All six candidates passed the formal gate before critic launch. The final
repository gate also passed: 58 critic tests and an 8,036-job Lean build, with
no proof placeholders or custom axioms.

## Limitations

This is a small, deliberately constructed benchmark from one theorem family.
It shows that the architecture can distinguish these defects; it does not yet
estimate performance on naturally occurring submissions or adversarial
wrong-but-compiling proofs. The four failing critics used the early
completeness checkpoint, so their token totals are unavailable. API cost was
also unavailable.

See `scores.json` for deterministic case-level results, `frozen-manifest.json`
for the frozen inputs, and each case's `review/` directory for the critic's
structured report and metrics.
