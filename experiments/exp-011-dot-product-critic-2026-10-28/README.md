# Floating-point dot-product critic benchmark

This held-out theorem-family experiment runs the complete critic architecture on
`roundedDotProduct_exists_perturbation`: frozen candidates, trusted Lean gates,
fresh isolated LLM critics, stable report validation, hidden expected labels,
and deterministic scoring.

It contains two correct candidates and four compiling semantic defects. Run:

```bash
python3 experiments/exp-011-dot-product-critic-2026-10-28/prepare.py
python3 experiments/exp-011-dot-product-critic-2026-10-28/preflight.py
python3 experiments/exp-011-dot-product-critic-2026-10-28/run_benchmark.py
```
