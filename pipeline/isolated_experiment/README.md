# Isolated floating-point proof pilot

The pilot formalizes Sahil Bhola's original Algorithm 1 and Theorem 3.1 from
the supplied three-page PDF. It is source-assisted formalization, not invention
of the mathematical proof. The first condition gets no Lean proof hints,
theorem skeleton, worked numerical example, previous project solution, or
conversation history. Its initial project contains only an import of Mathlib.
The second gets the identical assignment plus three generic Lean notes.

The controller runs from WSL. The evaluated actors and reviewers run inside
fresh Docker containers. No agent in this chat is used as a proof actor.

## Files and boundaries

- `Dockerfile`: pinned CLI runtime, ordinary Linux tools, non-root user.
- `run.py`: host controller for preparing, freezing, checking, launching,
  collecting, and independently evaluating outputs.
- `entry.py`: fresh CLI process, 20-minute builder or 5-minute reviewer limit,
  JSONL transcript and measured metrics. It does not inherit user configuration.
- `proxy.py`: CONNECT-only proxy allowing the model/auth service domains.
- `verify_candidate.py`: fresh, offline evaluation using the trusted verifier.

Run data lives under
`experiments/memory-ablation/2026-10-19-binary-tree-pilot/`.
The frozen manifest identifies inputs, memory provenance, versions, and hashes.

Containers mount only selected source files, a clean writable candidate project,
private output, read-only standard-library dependencies and Lean binaries, and
the minimum authentication file. Only the retrieved actor sees `/memory`.
The original repository, original project build cache, host home, Git history,
other run, evaluator prompt, hidden acceptance example, and Docker socket are
not mounted. All actor file and shell tools remain inside the container.

Actors have no direct external network route. A separate proxy allows only
`chatgpt.com`, `api.openai.com`, and `auth.openai.com` over TLS. Browser search
and host integrations are disabled. Authentication is never copied into run
artifacts, images, prompts, or command lines. It is mounted separately read-only;
the runtime home is disposable. This is a controlled research boundary, not a
claim of security against every hostile container escape or credential attack.

The CLI's internal sandbox bypass flag is used only inside this externally
restricted container. The root filesystem is read-only, the user is non-root,
Linux capabilities are dropped, and privilege escalation is disabled.

## Execution

From WSL, at the repository root:

```bash
docker build -t research-proof-pilot:2026-10-19 pipeline/isolated_experiment
python3 pipeline/isolated_experiment/run.py prepare
python3 pipeline/isolated_experiment/run.py preflight
python3 pipeline/isolated_experiment/run.py builders
python3 pipeline/isolated_experiment/run.py evaluate
python3 pipeline/isolated_experiment/run.py review
python3 pipeline/isolated_experiment/run.py summarize
python3 pipeline/isolated_experiment/run.py cleanup
```

Preparation refuses to rewrite frozen inputs. Builders refuse to overwrite an
existing attempt. Infrastructure-only repairs may be re-frozen before either
actor starts, with their previous hashes retained. They cannot change the
assignment or memory snapshot. Use a new experiment directory for a new attempt.

Preflight tests host/repository absence, protected files, condition-specific
memory visibility, missing hidden tests and socket, blocked GitHub and direct
egress, and a smoke build in a separate workspace. A connectivity-only model
request in a disposable session checks authentication without proof input.

## Acceptance and interpretation

The trusted evaluator copies only submitted Lean source into a fresh project,
imports every submitted module, restores the fixed build configuration, and
runs the repository's verification script offline. The independent critic gets
the original specification and candidate, but not the builder's narrative or
the other candidate. It checks algorithm fidelity, theorem assumptions, general
quantification, unchanged carries, multiplicities, depth, and the gamma bound.

A compiling unrelated or incomplete result is not a success. Critic approval
is evidence for semantic review, not a substitute for Lean or human judgment.
No critic feedback is used to extend one condition's builder budget.

Record failures, timeouts, API errors, and unknown costs honestly. Compiler
command events are a transcript-derived measure, not a count of individual
lemma attempts. API monetary cost is unknown under the current ChatGPT login.
The controller excludes connectivity checks and image preparation from builder
elapsed time; they remain visible infrastructure costs.

This single-assignment pilot uses manually curated generic memory partly
derived from prior work on this assignment. It demonstrates controlled access
and reuse machinery, not held-out transfer, statistically reliable savings, or
changes to model weights. Only after both runs finish may general verified
lessons be considered for promotion. Do not commit large build caches or secrets.
