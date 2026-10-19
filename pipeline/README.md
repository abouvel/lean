# Proving and artifact-learning pipeline

This directory contains executable machinery, not experiment results or memory.
Use [`experiment.py`](experiment.py) for the container pilot; see
[`REPRODUCE.md`](REPRODUCE.md) for checking results, offline replay, and fresh runs.
The scripts in `isolated_experiment/` are historical implementation details, not
separate workflows to choose between. Evidence belongs in `experiments/`;
searchable summaries belong in `artifacts/`.

Lean is the verifier, artifacts provide optional external memory, and Aristotle
is a slow fallback for an isolated blocked lemma.

```text
source theorem
→ choose memory mode: stateless or retrieved
→ search artifacts/index.md and relevant validated artifacts
→ reviewed Lean statement
→ compiling skeleton
→ small lemmas
→ local tactics and compiler-guided repair
→ further decomposition if blocked
→ Aristotle for one isolated blocked lemma
→ local verification
→ semantic audit
→ save raw run artifact
→ promote only compiler-verified reusable lessons
→ update artifact index
```

## Artifact rule

Follow [`../AGENTS.md`](../AGENTS.md). Before a stateful attempt, record which
artifact IDs were retrieved. After the attempt, save a structured record in
`artifacts/runs/`. Only general lessons backed by a successful full build may
be added to `artifacts/validated/`.

For stateless experiments, skip retrieval and record that explicitly. Never
place the evaluated theorem's completed proof in its retrieval set.

## Memory-ablation experiment

When testing whether artifacts help, create two isolated runs:

```text
same task specification and starting repository
├─ stateless: artifact retrieval prohibited
└─ retrieved: artifact snapshot available and retrieval logged
```

Assign the condition before work begins, freeze the retrieved condition's
artifact snapshot, and prevent either run from seeing the other's changes.
Keep the model, reasoning effort, tools, time limit, and verification command
fixed. Do not update shared validated memory until both runs finish.

Each run must record an `experiment_id`, `task_id`, condition, starting commit,
artifact snapshot, retrieved IDs, success, verification result, and all
available time/cost/attempt metrics. Detailed rules are in
[`../AGENTS.md`](../AGENTS.md#research-comparisons).

## Aristotle rule

Submit only after the statement compiles, local search and repair have failed, and the goal is a small lemma. Send a minimal staging project with no credentials or unrelated files. Accept the result only if the theorem statement is unchanged and the main project builds without `sorry`, `admit`, or new axioms.

Use [`verify.sh`](verify.sh) for the local build. It also rejects `sorry`,
`admit`, and project-defined `axiom` declarations before a result is accepted.
