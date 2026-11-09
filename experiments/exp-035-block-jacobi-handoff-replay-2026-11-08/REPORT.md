# Block Jacobi semantic replay

All twelve candidates blocked by the definition-only handoff in
[the original batch](../exp-034-block-jacobi-roundtrip-2026-11-06/REPORT.md)
were evaluated in a separate experiment. The pipeline now accepts inductive
types, including Lean structures, as construction entries and includes their
constructors in the translator bundle. Algorithm requirements remain in the
judge's rubric.

The original Lean verification and direct critic were reused after checking
candidate fingerprints, proof source hashes, and reviewer inputs. Each replay
ran a fresh blind translator and round-trip judge. No proof generation was
performed. The original experiment and its outcomes were left intact.

| Outcome | Stateless | Retrieved | Total |
| --- | ---: | ---: | ---: |
| Accepted | 6 | 4 | 10 |
| Human review needed | 0 | 2 | 2 |
| Infrastructure failure | 0 | 0 | 0 |

The direct critic passed both candidates sent to human review. The round-trip
judge returned uncertain. Those jobs are:

- `block-dot-product-trial-001-retrieved`
- `sequential-block-dot-trial-001-retrieved`

The original binary-tree direct-critic timeout and the two mixed-precision
Lean failures were outside this replay. Independent expert verdicts remain
pending. These selected replays do not establish a causal memory effect.

[Replay scorecard](scorecard.json) · [Frozen protocol](protocol.json)
