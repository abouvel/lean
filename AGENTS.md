# Research agent instructions

These instructions apply to the entire repository.

## Goal

Build Lean proofs through small, reviewable steps and preserve useful proof
experience as searchable artifacts. Lean compilation is the correctness gate.
Artifacts are external memory; they are not evidence that model weights changed.

## Before a proof attempt

1. For ordinary proof work, read `experiments/<id>/artifacts/index.md` for the
   relevant experiment. For experimental runs, follow the condition-specific
   access restrictions below instead.
2. Search its `artifacts/validated/` directory for theorem names, mathematical
   structures, tactics, and compiler errors relevant to the task.
3. Read a raw record in that experiment's `artifacts/` or `notes/` directory
   only when its index entry is relevant.
4. Record the artifact IDs actually used. Do not claim that retrieval helped
   unless the final run record identifies how it affected a decision.
5. If the task is an explicitly stateless experiment, do not search or read
   prior artifacts. Record `memory_mode: stateless` in the run artifact.

## During a proof attempt

- Keep the theorem statement separate from its proof.
- Translate the intended theorem back into ordinary mathematics before
  accepting a proof.
- Prefer small lemmas, local Lean compilation, and compiler-guided repair.
- Record important failed approaches and the exact diagnostic that changed the
  next decision. Do not store every routine compiler message.
- Use Aristotle only for an isolated blocked lemma after the statement compiles
  and local decomposition has been attempted.
- Never place secrets, `.env` contents, API keys, SSH keys, or credentials in an
  artifact or prompt record.

## Verification gate

Before calling a result verified, run:

```bash
bash pipeline/verify.sh
```

The result is verified only when the full build succeeds and the placeholder
and custom-axiom scans pass. Record unavailable timing, token, or cost data as
`unknown`; never invent measurements.

## Saving a run artifact

Create one Markdown summary in `experiments/<id>/artifacts/` and link it from
that directory's `index.md`. All proof attempts belong to an experiment; do not
create separate root-level `projects/` or `artifacts/` directories. Name the file:

```text
YYYY-MM-DD-short-description.md
```

Use these fields and sections:

```text
artifact_id
date
project
status: verified | failed | partial
memory_mode: stateless | retrieved
retrieved_artifacts
verification

Request
Target
Result
Decisions and reasoning
What worked
What failed
Reusable observations
Evidence
Remaining limitations
Metrics
```

Preserve the user's exact acceptance test when it is short. Link to code and a
project run record instead of copying large proofs or logs.

## Promoting reusable knowledge

Only promote a lesson into `experiments/<id>/artifacts/validated/` when:

1. the supporting Lean project passes `pipeline/verify.sh`;
2. the lesson is more general than one theorem;
3. the artifact identifies its supporting run IDs; and
4. limitations and counterexamples are retained.

Validated artifacts contain compact proof patterns, failure patterns, and
strategy rules. Raw evidence remains with its experiment; summaries stay in
the experiment's `artifacts/` directory.

## Updating the index

After adding or materially changing an artifact, update its experiment-local `artifacts/index.md`
with its ID, status, project, tags, one-sentence summary, and relative path.
Keep newest entries first. Do not delete failed runs merely because a later run
succeeded.

## Research comparisons

Use a memory-ablation experiment to test whether artifacts improve agent
performance. The two conditions are:

- `stateless`: do not read artifact indexes, validated lessons, experiment-local
  artifacts, prior experiment outputs, or earlier run records before or during
  the attempt.
- `retrieved`: use only the approved frozen memory snapshot, read its index,
  select relevant artifacts, and record every artifact ID actually opened and used.
  Do not read the full experiment-local artifact store unless it is explicitly
  part of the approved snapshot.

### Before an experiment

1. Write the task, acceptance tests, allowed tools, model, reasoning setting,
   time limit, and verification command before assigning a condition.
2. Freeze the artifact snapshot available to the retrieved condition. Record
   the Git commit or, if unavailable, the filenames and hashes.
3. Ensure the evaluated theorem and its completed proof are absent from the
   retrieval snapshot. Related proof strategies are allowed; the answer is not.
4. Assign the condition before the run. Prefer random assignment across many
   comparable tasks. For paired evaluation, use matched but distinct theorems
   to reduce direct answer leakage.
5. Start each run from the same repository state. Do not let changes from the
   first condition become input to the second condition.

### During an experiment

- Keep the theorem, model, reasoning effort, tools, timeout, and verification
  procedure fixed across conditions.
- Do not switch conditions after seeing whether the attempt is difficult.
- In `stateless` mode, ordinary source files and official library search remain
  allowed unless the experiment definition forbids them; only research-memory
  artifacts and prior run records are excluded.
- In `retrieved` mode, log each search query, opened artifact ID, and concrete
  decision influenced by retrieval.
- Do not create or update shared validated artifacts until both conditions for
  the comparison are complete.

### Required run metadata

Every experimental run artifact must include:

```text
experiment_id
condition: stateless | retrieved
task_id
model
reasoning_effort
starting_commit
artifact_snapshot
retrieved_artifacts
time_limit
verification_command
success
```

Also record, when available:

- wall-clock time;
- token usage and cost;
- compiler attempts;
- distinct failed strategies;
- Aristotle calls;
- final proof size;
- whether the result passed semantic review as well as compilation.

Use `unknown` for unavailable measurements. Never estimate missing values.

### After both conditions finish

1. Run the same verification gate on both outputs.
2. Compare success first, then time, cost, compiler attempts, and Aristotle use.
3. Report failures and regressions, not only improvements.
4. Separate retrieval from learning: improved performance shows benefit from
   external memory, not a change to model weights.
5. Only after comparison is complete may verified lessons be promoted into
   the experiment's `artifacts/validated/` for future experiments.
