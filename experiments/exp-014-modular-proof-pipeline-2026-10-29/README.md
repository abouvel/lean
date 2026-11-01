# Modular proof pipeline: frozen example and infrastructure validation

Branch: `codex/modular-proof-pipeline`.

The implementation is described in [the pipeline guide](../../pipeline/BATCH.md).
Its single-pass API is `stages.execute`; its single-job API is
`passes.run_condition`. The batch coordinator reuses those APIs in private
subprocesses with explicit model/build/RAM limits.

This experiment contains a frozen example with four queued jobs: two trials of
the binary-tree proof task, each stateless and retrieved. A separate disposable
Docker smoke workspace was used for infrastructure validation. No model job in
the queue has run.

```bash
python3 pipeline/batch.py status \
  --experiment experiments/exp-014-modular-proof-pipeline-2026-10-29

# This launches proof-building and critic agents and consumes model quota:
python3 pipeline/batch.py run \
  --experiment experiments/exp-014-modular-proof-pipeline-2026-10-29
```

For a different theorem list or concurrency setting, create a new plan with
`pipeline/batch.py plan`. Existing plans are immutable. All stateless jobs finish
before retrieved jobs start. Live artifacts are never added to the memory of
other jobs automatically.

See the [implementation record](artifacts/2026-10-29-modular-proof-pipeline.md),
[frozen plan](plan.json), [manifest](batch-manifest.json), and
[source diagram](architecture.drawio.xml).
