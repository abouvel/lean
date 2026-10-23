# Paired rerun with a 240-second critic budget

Date: 2026-10-23. Neither condition was accepted. This run does not establish
a benefit from retrieval, cost savings, or model learning.

## Fixed protocol

- Original Algorithm 1 / Theorem 3.1 task; import-only initial Lean project.
- gpt-6.1-sol, medium reasoning; stateless followed by retrieved.
- At most two passes per condition; 180 seconds per builder and **240 seconds
  per critic**, doubled before either condition began. No mid-run rule changes.
- Retrieved sees only the original frozen generic memory snapshot, not previous
  submissions, same-target answers, or stateless feedback.
- Fresh offline Lean verification precedes semantic review. Aristotle disabled.
- Earlier exp-003 was interrupted at the user's request and is not pooled here.

## Observed results

| Measure | Stateless | Retrieved |
| --- | --- | --- |
| Passes used | 2 | 2 |
| Offline Lean gates passed | 2/2 | 1/2 |
| Accepted full result | No | No |
| Final controller outcome | Infrastructure error: invalid critic report | Formal failure |
| Builder compiler-command events | 16 | 14 |
| Condition wall time | 530.18 s | 452.66 s |
| Builder time, total | 360.08 s | 360.10 s |
| Critic calls | 2 | 1 |
| Critic durations | 76.045 s; 67.092 s | 68.034 s |
| Critic timeouts | 0 | 0 |
| Aristotle calls | 0 | 0 |
| Complete token totals / cost | unknown / unknown | unknown / unknown |

All four builders reached their 180-second limits. Their saved code was then
evaluated; a builder timeout alone does not reject a valid saved submission.
Compiler-command events are logged commands, not independent theorem tests.
The retrieved aggregate `critic_seconds` is `unknown` in machine metrics because
pass two never invoked a critic; its one actual critic call took 68.034 seconds.

### Stateless

Pass one compiled but received a valid completeness rejection: reduction
termination, occurrence preservation, and the full original-input bound were
not established. Its checkpoint reached the builder as repair feedback.

Pass two compiled. Its critic finished normally and wrote a rejection, but used
`correction: null` for passed requirements; the validator requires strings.
It also wrote a completeness-phase report to `review.json`, whereas final reports
require `phase: final`. The controller stopped at the first schema error and
recorded `infrastructure_error`. The raw rejection identifies missing occurrence
conservation linking output leaves to the original input. It is evidence of the
critic's judgment, not an accepted machine verdict. Reports were not normalized
or relabeled after the run.

### Retrieved

Pass one compiled but the critic rejected missing backward-error obligations and
raised a concern about occurrence-indexed rounding errors. That valid checkpoint
was returned only to this condition's builder.

Pass two failed the offline build at `Submission.lean:353:47`, with this goal:

```text
⊢ 2 ::ₘ 2 ::ₘ 2 ::ₘ 2 ::ₘ {2} = ↑[2, 2, 2, 2, 2]
```

No second critic ran. The failed candidate was preserved without repair beyond
the pre-registered pass cap. The retrieval notes identify `pilot-general-lean-001`
and report using generic denominator-positivity, absolute-value, and rebuild
advice. That self-report does not establish a causal performance benefit.

## Interpretation and next step

All critics finished within the new limit, and both first-pass early rejection
checkpoints triggered repair correctly. The remaining report-contract mismatch
must be resolved before another model pair: specify an explicit JSON example
and consistent terminal-rejection routing, with tests for null corrections and
completeness versus final report filenames. Do not silently relax acceptance for
this completed run or interpret its unequal outcomes as a memory effect.

One paired task is insufficient for a reliable retrieval comparison even with
working infrastructure. External-memory reuse is not weight learning.

## Evidence and verification

- [Fixed configuration](experiment.json), [frozen hashes](frozen-manifest.json),
  [runtime identity](runtime.json), [isolation preflight](preflight.json).
- [Machine comparison](comparison.json), [JSON and Markdown artifacts](artifacts/index.md).
- Stateless [pass 1](stateless/passes/pass-001/pass.json),
  [pass 2](stateless/passes/pass-002/pass.json),
  [raw final critic report](stateless/passes/pass-002/stateless/review/review.json).
- Retrieved [pass 1](retrieved/passes/pass-001/pass.json),
  [pass 2](retrieved/passes/pass-002/pass.json),
  [failed build log](retrieved/passes/pass-002/retrieved/evaluation/verification.log).

Frozen-record verification passed after completion. Separately, the existing
repository proof library passed `bash pipeline/verify.sh` (8,036 build jobs and
placeholder/custom-axiom scans). That library result does not verify the isolated
retrieved candidate. The legacy `check` display prints `unknown` for bounded-run
summary fields; use `comparison.json` and per-pass records for measured results.
Experiment-owned containers and network were cleaned up; unrelated services
were left running. No lessons were promoted to validated memory.
