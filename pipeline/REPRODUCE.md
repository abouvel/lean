# Reproduce an experiment

Requirements: WSL/Linux, Python 3.10+, Lean v4.28.0, Docker Desktop with WSL
integration, and dependencies fetched using `lake exe cache get` from the root.
Keep the committed dependency lockfile. Fresh agents also require a Codex login
and model quota; pass `--auth /path/to/auth.json` or `RESEARCH_CODEX_AUTH`.
Never put credentials in the repository.

Build the runtime once, from the repository root:

```bash
docker build -t research-proof-pilot:2026-10-19 pipeline/docker
docker build -f pipeline/docker/Dockerfile.ready \
  -t research-proof-pilot-ready:2026-10-19 pipeline/docker
```

Then work from the experiment folder:

```bash
cd experiments/exp-001-binary-tree
python3 ../../pipeline/run.py check --config experiment.json
python3 ../../pipeline/run.py replay --config experiment.json --name replay-001
python3 ../../pipeline/run.py run --config experiment.json --name exp-002-binary-tree
```

| Action | Result | Model calls |
| --- | --- | --- |
| `check` (default) | Validate historical hashes and display results | No |
| `replay` | Saved proofs rebuilt in fresh offline containers | No |
| `run` | Fresh paired builders, offline verification, separate critics | Yes |

New outputs go into a **new sibling experiment folder** containing its own config,
inputs, memory, submissions, reviews, metrics, and `artifacts/` directory.
Existing names are rejected. `--lean` and `--packages` override dependency paths.
JSON configuration keeps the Python 3.10 runner dependency-free.

Fresh builders get an import-only project, never prior submissions or logs.
Both use the same model/settings; only retrieved sees the frozen memory.
Replay checks compilation/scans, not a new semantic review. The model can produce
different outputs on repeated runs. Aristotle and critic-assisted repair are disabled.

## Historical evidence

Experiment 1 includes a separate `interrupted/` pair, not pooled with the successful
pair. Its original IDs, prompts, manifests, transcripts, and numerical measurements
are retained. `relocation.json` maps old paths and pins original manifest hashes.
The checker validates original pipeline bytes in Git commit `e92d0ce`; the active
pipeline has been refactored and is **not** claimed byte-identical. Keep Git history
available. New runs hash the active code/config directly.

The base-image tag and apt packages are not fully locked, so image rebuilding is
not bit-for-bit reproducible. Actual image IDs are recorded in new `runtime.json`.
Offline replay still needs a working Docker engine. Never silently widen egress
permissions to force a run to succeed. Review new transcripts for secrets before committing.

## Local checks

From the repository root:

```bash
python3 -m unittest discover -s pipeline/tests -v
bash pipeline/verify.sh
```
