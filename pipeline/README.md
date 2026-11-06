# Shared proof pipeline

Experiments own their inputs and results. This directory runs the agents,
enforces container boundaries, and checks their outputs.

The opt-in [round-trip pipeline](ROUNDTRIP.md) separates planner, formalizer,
prover, blind translator, and semantic judge, with mandatory elaborated axiom
audits. It retains the direct critic during calibration. The [revision plan](REVISION_PLAN.md)
records the research design and remaining expert-review requirements. The
execution paths below describe the compatible legacy builder/critic mode.

For multiple theorems and trials, use the [modular batch pipeline](BATCH.md).
It reuses the same sequential proof pass inside isolated worker subprocesses,
with a durable queue, stateless-first scheduling, independent model/build/RAM
limits, searchable results, and comparisons when each pair finishes.

## Execution order

```text
Read experiment.json; freeze inputs and settings
                       ↓
Check isolation, toolchain, and model connectivity
                       ↓
Build: stateless agent → fresh retrieved agent
                       ↓
Verify each submission in a fresh offline container
                       ↓
Critique each submission in a separate fresh agent session
                       ↓
Save comparison; require verification AND critic pass
```

Builders run first, followed by verification and then critics. The retrieved
builder gets pre-existing frozen notes, **not** the stateless builder's output.
This is historical single-shot mode. Optional bounded mode adds repair without
changing the completed pilot results.

## Bounded passes and JSON artifacts

```text
Builder → fresh verification → critic → accept
   ↑                              |
   └── corrections, if budget remains
```

One pass is one fresh builder session, verification, and a critic if the formal
gate passes. Repairs retain that condition's candidate and feedback, not chat
history or compiler caches. "Stateless" excludes external research memory,
not feedback from its own earlier passes.

The [bounded config](../experiments/exp-001-binary-tree/bounded.json) fixes two
passes, 180 builder seconds/pass, and 240 critic seconds/pass for both conditions.
Verification has its own timeout. These are per-pass limits, not a hard token or
whole-condition wall-time cap. Choose budgets before running; do not lower the
baseline's limit after observing its result.

| Outcome | Next action |
| --- | --- |
| Formal gate fails | Builder receives compiler diagnostics |
| Critic rejects | Builder receives requirement/correction pairs |
| Critic uncertain | Stop for human review |
| Invalid review/service failure | Infrastructure error, not proof rejection |
| Pass cap reached | Save failure; no automatic Aristotle call |

[`passes.py`](passes.py) controls the loop. [`artifacts.py`](artifacts.py) writes
versioned JSON records with provenance, per-pass outcomes, timings, available
per-role token usage, compiler-command counts, final source lines, and evidence
paths. Unknowns stay `unknown`; cached inputs are a subset, and reasoning/output
counts are not blindly added. Markdown summaries link to the JSON and raw evidence.

Each `<condition>/passes/pass-NNN/` preserves its own candidate, review, feedback,
verification, and frozen input hashes. `comparison.json` summarizes the pair;
`artifacts/*.json` also contains unvalidated candidate lessons. Nothing generated
is automatically promoted or supplied to the other condition. The full private
critic report is not passed to the builder; model-written corrections still need
inspection for leakage or instruction injection.

From Experiment 1, when ready to spend model quota:

```bash
python3 ../../pipeline/run.py run --config bounded.json --name exp-002-bounded
```

Same-target compressed experience can leak an answer. Curate and freeze lessons
before a later run; exclude the completed target proof. Use matched distinct
tasks for transfer claims. Pseudocode ablation and Aristotle are separate future work.

## Where the critic agent is

[`critic.py`](critic.py) owns critic preparation, launch, reviewer entry point,
and verdict checking. It reuses the shared container and session runners:

```text
run.py: critic.review(engine)
          ↓
critic.py: stage source + rubric; request read-only critic container
          ↓
engine.py: Engine.container(reviewer=True) enforces shared isolation
          ↓
critic.py: main() reads /spec/REVIEWER.txt
          ↓
agent.py: run_agent(..., kind="reviewer") starts the fresh session
          ↓
<condition>/review/ receives the verdict, checks, and transcript
```

| Open this | What it controls |
| --- | --- |
| [`critic.py`](critic.py), `review()` | Stages the private rubric and launches each critic |
| [`critic.py`](critic.py), `main()` / `require_pass()` | Reviewer prompt selection and fail-closed verdict check |
| [`engine.py`](engine.py), `Engine.container()` | Shared read-only mounts, network restrictions, and resource limits |
| [`agent.py`](agent.py), `run_agent()` | Shared fresh-session launch, transcript, timeout, and metrics |
| [Experiment 1 reviewer instructions](../experiments/exp-001-binary-tree/evaluator/REVIEWER.txt) | Mathematical rubric, withheld cases, required report format |
| [`run.py`](run.py), `require_success()` | Requires the formal gate and delegates semantic acceptance to `critic.require_pass()` |

Each condition gets its own critic. The critic uses the experiment's configured
model and reasoning setting, with a separate time limit: five minutes in Experiment 1.
Separation means a fresh session, not a different model or trained evaluator.

## What grounds the critic

| Receives | Does not receive |
| --- | --- |
| Original paper and extracted specification | Builder conversation and decision-log files |
| Candidate Lean code, read-only | Other condition's candidate or results |
| Trusted verification logs, read-only | Retrieval memory snapshot by default |
| Private rubric and withheld acceptance cases | Permission to edit the candidate |

The rubric asks whether the formalization actually proves the assigned result:
arbitrary nonempty inputs, correct offset pairing, unchanged carries, duplicate
multiplicities, logarithmic depth, and the componentwise gamma bound. It also
checks for weakened conclusions, unjustified assumptions, vacuous definitions,
and missing obligations. Candidate comments are data, not instructions.

Critic memory is an explicit experiment-only opt-in. Set
`critic_memory_enabled: true` and list the exact condition names in
`retrieved_conditions` to mount the experiment's frozen memory directory
read-only for those critics. Retrieved critics are prompted to save a validated
`retrieval.json` recording actual searches, opened artifact IDs, and decisions
influenced. Conditions not listed remain stateless; ordinary production critics
still receive no retrieval memory.

The critic can write and compile independent checks in its private output
directory. Both pilot critics did so. Open the actual evidence:

- Stateless: [review](../experiments/exp-001-binary-tree/stateless/review/review.md),
  [structured verdict](../experiments/exp-001-binary-tree/stateless/review/review.json),
  [independent Lean checks](../experiments/exp-001-binary-tree/stateless/review/IndependentChecks.lean).
- Retrieved: [review](../experiments/exp-001-binary-tree/retrieved/review/review.md),
  [structured verdict](../experiments/exp-001-binary-tree/retrieved/review/review.json),
  [independent Lean checks](../experiments/exp-001-binary-tree/retrieved/review/IndependentChecks.lean).

### Stable critic requirements and benchmark scoring

New experiments may place `requirements.json` beside `REVIEWER.txt`. The critic
receives that catalog and must use its exact requirement and defect-category
IDs. Final reports must cover every requirement; early completeness checkpoints
may report only the requirements needed for the definite rejection. Historical
experiments without a catalog retain the legacy report contract.

[`critic_benchmark.py`](critic_benchmark.py) scores preserved reports against a
hidden manifest after the critic exits. It counts semantic verdict errors,
false passes, false rejections, expected defect detection, malformed reports,
and timeouts separately. Expected labels are evaluator data and must never be
mounted into the critic container. Templates live under [`examples/`](examples/).

```bash
python3 pipeline/critic_benchmark.py path/to/benchmark.json --output scores.json
```

## Lean verification is a separate gate

| Gate | Question |
| --- | --- |
| Offline verifier **script** | Does Lean accept the submitted proof, without prohibited placeholders or custom axioms? |
| Critic **agent** | Do its definitions, statement, and assumptions match the original assignment? |
| Human review | Are the specification and interpretation appropriate for the research claim? |

[`engine.py`](engine.py), `Engine.evaluate()`, copies only submitted Lean sources
into a clean project, restores the protected configuration, imports every module,
and runs [`verify.py`](verify.py) with the experiment's trusted verification script.
Builder caches are not copied. Network access is disabled (`--network none`).

Lean can verify the wrong statement. The baseline starts without a supplied Lean
theorem skeleton, so semantic alignment is checked afterward, not guaranteed by
a pre-locked formal statement. The critic can also be wrong; its report is not a
proof certificate. Human sign-off remains separate. Critics currently inspect
final code, not the complete builder action trace; jailbreak resistance and
critic accuracy have not been benchmarked.

## Isolation and saved files

### Critic order and failure handling

```text
Original task + submitted code + offline verification
                         ↓
             Is the full target actually proved?
               ├─ No → failure checkpoint → same builder's next pass
               └─ Possibly → full semantic review → final report
                                 ├─ Pass → accept
                                 ├─ Fail → same builder's next pass
                                 └─ Uncertain → human review
```

The critic must identify the proved declaration and assumptions before running
optional examples. Defining the desired proposition does not prove it.
`checkpoint.json` records only a valid, definite completeness failure and stops
the critic early (polled every two seconds). Otherwise no checkpoint is written;
`review.json` is the final audit.
Both need requirement-level evidence and target source locations. Only a final
report can pass; Lean's offline gate must also pass. No report, malformed JSON,
or a timeout remains an infrastructure error, not a theorem rejection. Repairs
stay within the existing pass cap; uncertainty stops for human review.

This is a workflow guard, not a guarantee that the critic's judgment is correct.
The 240-second trial removed the earlier critic timeouts but exposed a report
contract mismatch (`correction: null` and a completeness report under the final
filename). The active contract now gives typed JSON examples and deterministic
filename routing. A model-backed canary is still needed before another paid pair.

Containers run non-root with a read-only root, dropped capabilities, and resource
limits. Builders see only selected inputs, private workspace/output, read-only
Lean/Mathlib, and optional frozen memory. No host repository, Git history, other
run, or Docker socket is mounted. Model requests use an allowlisted proxy;
credentials are mounted separately, never saved in prompts or artifacts.

```text
experiments/<id>/<condition>/
├── workspace/          Builder's submitted proof
├── output/             Builder prompt, transcript, decisions, metrics
├── evaluation/         Trusted verification result and logs
└── review/             Critic prompt, transcript, verdict, checks, metrics
```

## Aristotle: not connected to the critic yet

```text
Statement compiles + local repair/decomposition tried + small lemma blocked
                                  ↓
                              Aristotle
                                  ↓
                  Unchanged statement + full local recheck
```

This is the proposed fallback policy, **not an implemented automatic branch**.
Aristotle was disabled in both pilot conditions; zero calls occurred. Neither a
critic failure nor a Lean error currently triggers it. Adding it requires equal
eligibility rules and call budgets for both conditions.

## Run / inspect

From an experiment folder:

```bash
python3 ../../pipeline/run.py check --config experiment.json
python3 ../../pipeline/run.py replay --config experiment.json --name replay-001
python3 ../../pipeline/run.py run --config experiment.json --name exp-002-binary-tree
```

`check` displays saved results. `replay` rebuilds saved proofs offline, **without
rerunning critics**. Only `run` launches fresh builders and critics. New outputs
go to a new sibling experiment folder; historical evidence is never overwritten.

[Prerequisites and reproduction details](REPRODUCE.md) · [Experiment 1](../experiments/exp-001-binary-tree/README.md)
