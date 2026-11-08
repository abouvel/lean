# Block Jacobi batch results

The batch ended on November 8, 2026, with terminal results for all 20 jobs.
The supplied manuscript and the ten individual task packets are saved in
[the source experiment](../exp-033-block-jacobi-proof-packets-2026-11-06/README.md).
Each result was attempted independently in a fresh Lean workspace, once per
memory condition, with the paper available as mathematical source material.

| Outcome | Stateless | Retrieved |
| --- | ---: | ---: |
| Lean and both semantic reviewers passed | 3 | 2 |
| Lean passed and the run hit an infrastructure error | 6 | 7 |
| Lean verification failed | 1 | 1 |

The real-arithmetic Block Jacobi theorem passed in both conditions.
Binary-tree reduction and triangular solve passed without notes. Triangular
update passed with notes. The final mixed-precision theorem failed Lean
verification in both conditions. Independent expert verdicts are pending.

Twelve infrastructure errors occurred when the handoff required selected
constructions to be definitions. In every case the named declaration existed
in the elaborated context as an inductive type. The remaining infrastructure
error was a direct-critic timeout. These jobs have no final paired semantic
verdict. The 3–2 acceptance split does not support a memory comparison with
so many jobs blocked before the round trip.

For a follow-up, allow supported inductive declarations in the construction
handoff and test a fixture with a structure or inductive trace. Replay the
semantic stages on the archived, fingerprinted candidates in a new experiment.
Keep the original failed outcomes and treat the two mixed-precision formal
failures as a separate proof task.

[Scorecard](scorecard.json) · [Job results](artifacts/jobs.md) ·
[Pair comparison](comparison.json)
