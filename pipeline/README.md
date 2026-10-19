# Shared proof pipeline

Experiments own their inputs and results; this directory owns the machinery.

```text
experiment.json + inputs + frozen memory
                    ↓
         run.py → isolation preflight
                    ↓
         Builder agent: Lean repair
                    ↓
         Fresh offline verifier script
                    ↓
         Separate critic agent
                    ↓
         Experiment-local results
```

Stateless runs first; retrieved starts fresh with **pre-existing frozen notes**,
not the first run's answer. Critics inspect the original source, read-only
candidate, verification logs, and withheld tests. No critic repair loop is enabled.

| File | Role |
| --- | --- |
| `run.py` | Config, input freezing, new experiment creation, outcome checks |
| `engine.py` | Container isolation, builders, verification, critics |
| `agent.py` | Fresh model session, transcript, timing/token records |
| `verify.py` | Offline build and placeholder/custom-axiom scans |
| `verify.sh` | Main repository verification gate |
| `docker/` | Dockerfiles and allowlisted network proxy |

Builder containers get selected inputs, private workspace/output, read-only
Lean/Mathlib, and optional memory. No host repository, Git history, other run,
or Docker socket. Non-root, read-only root, dropped capabilities, resource limits.
Model access uses a restricted proxy; verification has no network.
Credentials are separately mounted, never saved in prompts or artifacts.

## Aristotle policy

```text
Compiling statement + failed local repair/decomposition + blocked small lemma
                                  ↓
                              Aristotle
                                  ↓
                  Unchanged statement + full local recheck
```

This is a future fallback policy, **not an automatic implemented branch**.
Aristotle is disabled in the current pair. Both conditions must have equal access
and budgets if it is added. Lean validity, semantic fidelity, and process fidelity
are different checks; human statement review remains necessary.

[Run commands and prerequisites](REPRODUCE.md) · [Experiment 1](../experiments/exp-001-binary-tree/README.md)
