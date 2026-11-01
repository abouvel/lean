# Dot-product critic memory ablation

This preregistered paired experiment compares the same six compiling
floating-point dot-product candidates under two critic conditions:

- `stateless`: no research-memory mount;
- `retrieved`: a read-only, pre-dot-product critic-memory snapshot plus a
  required retrieval audit log.

The model, reasoning effort, rubric, requirement catalog, formal gate, time
limit, candidates, and hidden labels are identical. Condition order is frozen
and counterbalanced. The retrieved snapshot contains no dot-product candidate,
verdict, or expected label.

Run `prepare.py`, then `preflight.py`, then `run_benchmark.py`.
