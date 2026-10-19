# Shared proof pipeline

Experiments own their inputs and results. This directory runs the agents,
enforces container boundaries, and checks their outputs.

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
The current critic is a post-hoc reviewer; it does not send repair feedback.

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
| Trusted verification logs, read-only | Retrieval memory snapshot |
| Private rubric and withheld acceptance cases | Permission to edit the candidate |

The rubric asks whether the formalization actually proves the assigned result:
arbitrary nonempty inputs, correct offset pairing, unchanged carries, duplicate
multiplicities, logarithmic depth, and the componentwise gamma bound. It also
checks for weakened conclusions, unjustified assumptions, vacuous definitions,
and missing obligations. Candidate comments are data, not instructions.

The critic can write and compile independent checks in its private output
directory. Both pilot critics did so. Open the actual evidence:

- Stateless: [review](../experiments/exp-001-binary-tree/stateless/review/review.md),
  [structured verdict](../experiments/exp-001-binary-tree/stateless/review/review.json),
  [independent Lean checks](../experiments/exp-001-binary-tree/stateless/review/IndependentChecks.lean).
- Retrieved: [review](../experiments/exp-001-binary-tree/retrieved/review/review.md),
  [structured verdict](../experiments/exp-001-binary-tree/retrieved/review/review.json),
  [independent Lean checks](../experiments/exp-001-binary-tree/retrieved/review/IndependentChecks.lean).

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
