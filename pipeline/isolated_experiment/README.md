# Isolated proof pipeline

Formalize Algorithm 1 and Theorem 3.1 from the supplied binary-tree paper.
The mathematical proof is input; the agents construct the Lean formalization.

## Flow

The WSL controller runs each condition separately, stateless first:

```text
Freeze task, settings, and memory
               ↓
Check container isolation
               ↓
Builder AGENT: implement → compile → repair
               ↓
Offline SCRIPT: fresh Lean build + scans
               ↓
Critic AGENT: compare specification + run independent checks
               ↓
Record outcome, metrics, and artifacts
```

Failure is recorded, not accepted. Critics do not send repair feedback in this pilot.

| Condition | Builder input |
| --- | --- |
| Stateless | Original PDF/text + clean Lean project |
| Retrieved | Identical input + frozen generic Lean notes |

Neither gets the existing Lean solution, chat history, or worked example.
Retrieved does **not** get the stateless run's output. Compare results only after both finish.

## Isolation

```text
HOST                         BUILDER CONTAINER
Selected read-only inputs ──→ /spec, Lean/Mathlib
Retrieved condition only ──→ /memory
                             /workspace  private, writable
                             /output     private, writable
```

No host repository, Git history, other run, or Docker socket is mounted.
Non-root user; read-only root; dropped capabilities; resource limits.
Model access uses an allowlisted proxy; verification uses `--network none`.
The model runs remotely; shell/file tools run inside the container.
Credentials are mounted separately, never included in artifacts or images.

## Correctness gates

| Check | Grounding |
| --- | --- |
| Lean verifier | Submitted sources rebuilt without builder caches; placeholder/custom-axiom scans |
| Separate critic | Original source, read-only candidate, verification logs, withheld tests |
| Semantic review | Pairing, unchanged carry, multiplicities, logarithmic depth, gamma bound, assumptions |

Critics use fresh sessions without builder conversations. Human statement review
remains necessary: compilation can prove the wrong specification. The pilot does
not establish IEEE 754 bit behavior, jailbreak resistance, or complete action-trace fidelity.

## Aristotle: optional fallback

```text
Statement compiles + local repair/decomposition tried + isolated lemma blocked
                                  ↓
                              Aristotle
                                  ↓
                 Unchanged statement + full local recheck
```

**Disabled in both pilot conditions; zero calls.** Future comparisons must give
both conditions the same eligibility rule and call budget.

## Run / inspect

From the repository root in WSL:

```bash
python3 pipeline/experiment.py check
python3 pipeline/experiment.py replay --run-id replay-001
python3 pipeline/experiment.py run --run-id pair-002
```

`check`: saved evidence. `replay`: offline rebuild, no agents. `run`: fresh builders + critics.
New IDs prevent overwrites. [Prerequisites and details](../REPRODUCE.md).

| Location | Role |
| --- | --- |
| `../experiment.py` | Public entry point |
| `run.py`, `retry_pair.py` | Host orchestration and container boundaries |
| `entry.py` | Launch fresh builder/critic sessions |
| `verify_candidate.py` | Trusted offline verification |
| `../../experiments/` | Frozen inputs, candidate proofs, transcripts, results |
| `../../artifacts/` | Searchable summaries and verified lessons |

[Completed pilot report](../../experiments/memory-ablation/2026-10-19-binary-tree-pilot-gpt61/REPORT.md).
External memory is reuse, not changed model weights; one pair does not establish learning or savings.
