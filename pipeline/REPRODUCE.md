# Reproduce the binary-tree pilot

Run from WSL/Linux at the repository root. The public entry point is
`python3 pipeline/experiment.py`; `isolated_experiment/` is its implementation.
The historical date-specific scripts remain unchanged because past manifests hash them.
The updated implementation README is the sole documentation exception: the entry
point verifies its original bytes in Git commit `e92d0ce` against the recorded
hash. No executable, specification, or memory hash is exempted. Keep that commit
available when cloning history. Use the public entry point, not the old scripts directly.

## Prerequisites

- Docker Desktop running with integration enabled for your WSL distribution.
- Python 3.10+ and Lean v4.28.0 installed through elan.
- Dependencies installed: `lake exe cache get`, using the committed manifest.
  Do not run `lake update` just to reproduce a run; it can change the lockfile.
- For fresh agents only: a working Codex login and available model quota.
  Pass its file with `--auth /path/to/auth.json` or `RESEARCH_CODEX_AUTH`.
  It is mounted separately; do not copy it into this repository.

Build the two runtime layers once:

```bash
docker build -t research-proof-pilot:2026-10-19 pipeline/isolated_experiment
docker build -f pipeline/isolated_experiment/Dockerfile.ready \
  -t research-proof-pilot-ready:2026-10-19 pipeline/isolated_experiment
```

CLI, Lean, and Mathlib versions are pinned. The base-image tag and apt packages
are not fully locked, so rebuilding the image is not bit-for-bit reproducible.
Each new execution records the actual local image ID in `runtime.json`.

## Three commands

```bash
python3 pipeline/experiment.py check
python3 pipeline/experiment.py replay --run-id replay-001
python3 pipeline/experiment.py run --run-id pair-002
```

| Command | What it does | Model calls |
| --- | --- | --- |
| `check` | Checks frozen-input hashes and summarizes the saved comparison. | None |
| `replay` | Rebuilds saved Lean submissions in new offline containers. | None |
| `run` | Fresh builders, offline verification, independent critics, comparison. | Yes |

New directories go under `experiments/memory-ablation/<run-id>/`. Existing names
are rejected. Failed attempts remain available for inspection. Use `--lean` and
`--packages` if dependency locations differ. No original Downloads PDF is needed:
the template includes the original frozen source and its text extraction.

Runner safety tests (no Docker/model needed):

```bash
python3 -m unittest discover -s pipeline/tests -v
bash pipeline/verify.sh
```

The fresh pair uses the saved model/effort, prompts, 20-minute builder and
5-minute critic limits. Stateless runs first; retrieved receives the same
**previously frozen generic notes**, not the first run's proof. The template
contains prior answers, but those are never copied or mounted into fresh builders.
Both conditions have Aristotle disabled. Model availability and stochastic
generation can change outcomes. A failing preflight stops the run; never widen
the network allowlist automatically to force success.

Replay checks compilation/scans only; it does not rerun critics or establish a
new semantic approval. A fresh pair also needs human review of its final statement.
The current critics inspect sources, not full action traces; process fidelity
is a separate audit. Frozen source/model settings are not a claim of immutable
host caches, a bit-identical runtime, or a security certification.

## Storage policy

- Keep specifications, submitted `.lean` files, manifests, reports, important
  diagnostics, transcripts, and metrics as experimental evidence.
- Keep one concise searchable summary in `artifacts/runs/`; link to evidence.
- Put general verified lessons in `artifacts/validated/`, only after comparison.
- Ignore `.lake/`, Python caches, replay output, and slide-rendering scratch files.
- Existing historical directories are retained; do not move files referenced by
  frozen manifests. New experiment logs do not also need `projects/*/runs/` copies.
- Do not commit a new run until its prompts/transcripts have been checked for
  credentials and private material. Unknown cost remains `unknown`.
