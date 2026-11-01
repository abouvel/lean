# Modular single-pass and batch proof pipeline

artifact_id: `2026-10-29-modular-proof-pipeline`
date: 2026-10-29
project: proof-pipeline-infrastructure
status: verified
memory_mode: retrieved
retrieved_artifacts: `[pilot-general-lean-001]`
verification: 72 pipeline tests passed; real archived-runtime Docker/Lean preflight passed; `bash pipeline/verify.sh` passed 8,036 jobs and placeholder/custom-axiom scans; `git diff --check` passed.

experiment_id: `exp-014-modular-proof-pipeline-2026-10-29`
condition: retrieved
task_id: build-modular-proof-pipeline
model: unknown (no evaluated model sessions invoked)
reasoning_effort: unknown
starting_commit: `a42eeb51fa8a9ee36f5a6027bd840189198ab283`
artifact_snapshot: `batch-manifest.json` SHA-256 `e16b7aeba75a60a97ab8cd89966734bb2da6faa6bb20de7dbb439ee219a75bf6`
time_limit: unknown (infrastructure implementation); queued jobs have frozen 3,600-second deadlines
verification_command: `bash pipeline/verify.sh`
success: true (infrastructure validation)

## Request

"make sure the single pass is very modular and build out the larger pipeline.
make a new git branch for this and build it out"

The attached draw.io file describes theorem/trial/condition jobs, a bounded
parallel coordinator, private result bundles, stateless-first ordering, and
comparison after each pair finishes.

## Target

Extract reusable single-pass stages and a single-condition API. Add a frozen
offline plan, durable queue, isolated subprocess workers, resource admission,
heartbeat/status, timeouts, interruption recovery, deterministic result
validation, full-text result search, and incremental paired comparisons.

## Result

Implemented on branch `codex/modular-proof-pipeline`. The final frozen example
contains four queued jobs: two trials of the existing binary-tree proof task
under stateless/retrieved conditions. No proof-building or critic model calls
were made for this implementation task. The smoke build used a disposable
stateless workspace; its success is infrastructure evidence, not a completed
proof-agent experiment.

## Decisions and reasoning

- `stages.py` separates builder, verifier, critic, and repair feedback. Existing
  bounded repairs reuse these stages; `passes.run_condition` exposes one job.
- `batch.py` plans offline and runs an asyncio coordinator with a SQLite queue.
  All stateless jobs finish before retrieved jobs start. Slots refill when a
  job finishes; jobs do not wait for an entire wave.
- `worker.py` runs one private proof loop. `resources.py` provides process-shared
  model/build leases and atomic heartbeat files.
- Agents can invoke Lean, so model stages reserve a build slot too. RAM
  admission accounts for each worker's container budget and overhead.
- Both coordinator and worker implementation bytes are archived and used for
  execution. Jobs have independent task/memory copies, protected mounts, and
  same-condition repair feedback.
- Candidate lessons become searchable after collection, but are not
  automatically promoted or supplied to running jobs.
- Reading `pilot-general-lean-001` and its frozen index established that the
  sample memory contains only generic tactic/compiler notes. This informed the
  example's explicit target-answer-exclusion review; no performance benefit
  from retrieval is claimed.

## What worked

- All 72 regression/integration tests passed.
- Real subprocess tests demonstrated concurrent execution, slot refill,
  stateless-first ordering, cross-process model/build limits, timeout cleanup,
  missing/invalid-result handling, queue recovery, duplicate-coordinator
  rejection, frozen input checks, and artifact search.
- Planning made private identical task copies and rejected a RAM budget that
  could not cover the requested concurrency.
- The final archived runtime passed Docker isolation checks and an 8,028-job
  Lean smoke build, with direct egress blocked and expected tool versions.
- The repository-wide 8,036-job gate and placeholder/custom-axiom scans passed.

## What failed

Two initial controller tests still patched the previous `passes.review`
boundary after the stage extraction. They were updated to patch the actual
`stages.review` boundary and passed. The initial offline plan in `exp-013`
predates the final coordinator archive dispatch; its evidence is retained.
The final reviewed plan is `exp-014`.

## Reusable observations

Resource control belongs at stage boundaries; proof stages remain independently
callable. Archive the scheduler as well as workers to preserve an experiment's
execution policy. A cancelled running job must retain evidence and become an
infrastructure error; silently replaying it mixes attempts. Shared result
tables must not overwrite curated research summaries.

## Evidence

- [Frozen plan](../plan.json)
- [Frozen manifest](../batch-manifest.json)
- [Source diagram](../architecture.drawio.xml)
- [Docker smoke script](../docker_smoke.py)
- [Docker preflight evidence](../docker-smoke-run/preflight.json)
- [Pipeline guide](../../../pipeline/BATCH.md)
- [Coordinator integration tests](../../../pipeline/tests/test_batch.py)
- [Resource tests](../../../pipeline/tests/test_resources.py)

## Remaining limitations

No live proof-agent throughput or cumulative-transfer experiment was run.
Concurrency defaults have not been optimized empirically. RAM admission uses
an explicit configured capacity rather than measuring available host RAM.
Build-slot reservation over whole model sessions is conservative. Interrupted
jobs require a new experiment to retry; queued jobs can resume. Candidate
lesson curation and future memory freezing remain explicit experiment steps.

## Metrics

- pipeline tests: 72 passed
- repository Lean build: 8,036 jobs, passed
- Docker smoke Lean build: 8,028 jobs, passed
- queued example jobs: 4
- completed model jobs in this example: 0
- model calls: 0
- Aristotle calls: 0
- API cost, token usage, implementation wall time: unknown
- proof-agent performance and semantic success: not measured
