# Original floating-point proof: isolated pilot results

Date: 2026-10-19. Experiment: `2026-10-19-binary-tree-pilot-gpt61`.

## Outcome

Both fresh agents formalized Sahil Bhola's original Algorithm 1 and Theorem 3.1.
Both candidates passed the trusted offline build and placeholder/custom-axiom
scans. Separate critic sessions accepted both and compiled independent checks
against the original source. No Aristotle calls occurred.

The memory-enabled run was **17.2% slower** and used more tokens in this pair.
This pilot demonstrates isolation, source delivery, artifact retrieval, and
verification. It does not demonstrate a learning or savings benefit.

## What the agents received

Both received the original three-page PDF and its text extraction, including
the mathematical proof and Algorithm 1. This was **source-assisted
formalization**, not discovery of the mathematical proof from scratch.
The original TeX was unavailable; no invented TeX transcription was substituted.

The baseline received **no Lean theorem skeleton, tactics, proof recipe,
worked numerical example, earlier chat, prior project proof, or run artifacts**.
Its Lean source initially contained only `import Mathlib`, with the surrounding
build configuration supplied as infrastructure.

The retrieved condition received identical starting inputs plus a read-only
snapshot containing one manually curated generic artifact: an absolute-value
lemma name, advice about positive denominators, and a note about stale imports.
The snapshot excluded the target's statement, completed proof, tree invariants,
logarithmic-depth argument, and numerical example. Its provenance is prior work
on this assignment, so this is not an unseen-task transfer experiment.

The retrieved actor opened `pilot-general-lean-001` and logged intended uses in
[retrieval.md](retrieved/output/retrieval.md). The transcript records the actual
file reads. These observations establish access and reported use, not a causal
benefit from any particular lesson.

## Measured results

| Metric | Stateless | Retrieved |
| --- | ---: | ---: |
| Builder model / effort | gpt-6.1-sol / medium | gpt-6.1-sol / medium |
| Builder time limit | 1,200 s | 1,200 s |
| Builder elapsed time | 458.993 s (7:39) | 538.043 s (8:58) |
| Builder exit code / timeout | 0 / no | 0 / no |
| Trusted build and scans | pass | pass |
| Independent critic | pass | pass |
| Cumulative input tokens | 1,278,341 | 1,660,099 |
| Cached input tokens (subset) | 1,221,248 | 1,591,040 |
| Input tokens excluding cached subset | 57,093 | 69,059 |
| Output tokens, as reported by CLI | 22,111 | 25,039 |
| Reasoning output tokens, separately reported | 8,351 | 9,286 |
| Compiler-command events | 24 | 27 |
| Submitted Lean source lines | 490 | 549 |
| Offline verification time | 14.871 s | 23.325 s |
| Critic elapsed time | 107.994 s | 132.397 s |
| Critic input / output tokens | 338,475 / 5,417 | 312,697 / 6,099 |
| Aristotle calls | 0 | 0 |
| Monetary cost | unknown | unknown |

Input tokens are cumulative across model calls, not the size of a single prompt.
Cached inputs are a subset, not additional tokens. The provider's output and
reasoning fields are retained separately without adding potentially overlapping
counts. Compiler-command events include exploratory checks, not individual
proof obligations or independent tests. Source length is not a quality score.

Relative to the baseline, the retrieved run used 29.9% more cumulative input
tokens and 13.2% more output tokens. No dollar savings are claimed: both used a
ChatGPT login, and actual API billing cost was not exposed.

## Independent correctness and fidelity checks

The trusted evaluator copied only submitted Lean sources into fresh offline
projects, restored fixed configuration, imported all submitted modules, and ran
the trusted `bash pipeline/verify.sh` gate. Actor-generated build caches were
not transferred. Critic sessions received the original specification and
candidate, without the builder's narrative or the other candidate.

Both critics compiled the previously withheld acceptance trace:

```text
[2,3,4,5,6]
[7,9,4]
[11,9]
[20]
```

They also checked singleton/odd inputs, duplicate occurrences, unchanged
subtree carries, the logarithmic depth, and the per-input gamma bound.
Symbolic arbitrary-operation checks distinguish a true carry from an added
operation with zero. The retrieved candidate's critic additionally compiled
nonzero-rounding-error cases. Audited declarations used only `propext`,
`Classical.choice`, and `Quot.sound`; no project-defined axioms or placeholders.

These checks support the abstract deterministic relative-error result. They do
not verify IEEE bit behavior, overflow detection, physical parallel scheduling,
or the separate probabilistic theorem. The candidate theorems are scalar;
componentwise application follows by scalar instantiation. The stateless
critic also compiled an arbitrary-coordinate specialization.

Both candidates received a critic pass with no substantive missing obligations.
This is not a measurement of critic accuracy: no seeded-defect benchmark was
run. No human sign-off is claimed; the code and reports are ready for review.

## Containerization and process fidelity

Each actor ran as a non-root user with a read-only container filesystem,
dropped capabilities, disabled privilege escalation, private writable candidate
and output directories, and a disposable session home. Source/configuration,
standard libraries, Lean binaries, and memory were mounted read-only. Only the
retrieved actor had `/memory`.

The source repository, existing solution, prior conversation, other run,
answer-bearing project cache and Git history, hidden evaluator prompt, host
home, and Docker socket were not mounted. All actor shell/file tools executed
inside the container. Internal Docker networking blocked direct external
connections; a CONNECT proxy permitted only fixed model/authentication and
observed model-attachment service hosts. GitHub remained blocked. Authentication
was mounted separately and never copied into experiment artifacts or images.

All configured access/toolchain probes and the separate smoke build passed.
See [preflight.json](preflight.json). The exact image ID is recorded there.

**Observed boundary interaction:** the retrieved actor attempted to rewrite
`Research.lean` to add an import. The read-only mount rejected it with
`cannot create Research.lean: Read-only file system`. It then retained the fixed
root and imported its modules through the allowed `Research/Submission.lean`.
The final build passed and no protected file changed.

This is a blocked protected-file write, not evidence of deliberate jailbreak
intent. It shows why access controls should enforce boundaries instead of
depending on instructions or final-code critique alone. The critics reviewed
final artifacts; this action-level finding came from the host transcript audit.
A future process critic should also receive a sanitized action trace.
No adversarial jailbreak resistance benchmark was run.

## Preserved unsuccessful attempts

The first pair used the configured local model, `gpt-5.6-sol / medium`.
The service interrupted the baseline after 156.308 seconds and prevented the
retrieved run from starting substantively, with `Selected model is at capacity`.
Their transcripts, partial source, metrics, and failed acceptance remain in the
[separate interrupted pair](interrupted/README.md).

The new pair fixed `gpt-6.1-sol / medium` for both conditions before either
started. It also fixed login-shell binary discovery and allowed the observed
model attachment hosts. These are separate experiments; results are not pooled.

## Interpretation and next step

- Both agents could formalize the original task without a supplied Lean solution.
- The container boundary worked for the tested access and write attempts.
- Retrieval occurred, but this small generic snapshot produced no observed
  runtime or token advantage in this pair.
- A fresh critic can check the final proof and independently compile withheld
  cases; tracing process compliance requires the action log as well.

There is one run per condition, a fixed sequential order, a shared machine and
dependency/page caches, provider prompt caching, and model sampling variation.
These results cannot establish that memory generally helps or harms, measure
plasticity, or imply changed model weights. Memory preparation/setup costs are
not included in builder times and were not fully measured.

The next comparison should use repeated held-out formalization tasks, a frozen
snapshot without their solutions, randomized/counterbalanced order, and a
separate test of critic-assisted repair. Retain regressions and failures.

## Evidence

- [Exact frozen inputs, settings, provenance, and hashes](frozen-manifest.json)
- [Machine comparison](comparison.json)
- [Stateless proof](stateless/workspace/Research/Submission.lean)
- [Retrieved main theorem](retrieved/workspace/Research/FloatingPoint.lean)
- [Retrieved tree implementation](retrieved/workspace/Research/BinaryTree.lean)
- [Stateless metrics](stateless/output/metrics.json) and [decisions](stateless/output/decisions.md)
- [Retrieved metrics](retrieved/output/metrics.json) and [decisions](retrieved/output/decisions.md)
- [Stateless critic](stateless/review/review.md) and [independent checks](stateless/review/IndependentChecks.lean)
- [Retrieved critic](retrieved/review/review.md) and [independent checks](retrieved/review/IndependentChecks.lean)
- [Shared pipeline](../../pipeline/README.md) and [reproduction notes](../../pipeline/REPRODUCE.md)

The pre-existing main research proof was left unchanged and independently
passed the repository verification gate during the experiment. Its build is
separate from the candidate verification results above.
