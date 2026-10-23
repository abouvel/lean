# Revised bounded experiment — 2026-10-23

## Outcome

**Executed, but inconclusive for the memory comparison.** Both candidates passed
the offline Lean build/scans. Both critics reached their 120-second limits before
writing a structured verdict. Each condition therefore stopped after pass 1 as
`infrastructure_error`; neither candidate was accepted. No repair pass occurred.

Compilation is not completion: post-run source inspection shows that both
candidates define the `BackwardStable` proposition without proving the complete
backward-error theorem. The retrieved builder explicitly records this remaining
obligation in its [decision log](retrieved/passes/pass-001/retrieved/output/decisions.md).
This is a post-run observation, not a completed critic verdict or human sign-off.

## Fixed protocol

- Same original paper, mathematical proof, pseudocode, and clean Lean scaffold.
- `gpt-6.1-sol`, medium reasoning; stateless first, retrieved second.
- Maximum two passes per condition; 180 builder seconds/pass and 120 critic seconds/pass.
- Fresh builder, fresh offline evaluator, and separate fresh critic containers.
- Only retrieved received the existing frozen generic notes. Neither received
  the other condition's new proof, transcript, or JSON artifacts.
- No Aristotle, critic retries, budget extensions, or model substitutions.
- All access/toolchain preflights and the model connectivity request passed.

The configured limits were not changed after observing the baseline.
The pass cap is a ceiling, not a requirement to run pass 2 after infrastructure failure.
Builder timeouts allow verification of saved partial code; critic timeouts do not
authorize acceptance or manufacture repair feedback.

## Measured results

| Metric | Stateless | Retrieved |
| --- | ---: | ---: |
| Passes used / maximum | 1 / 2 | 1 / 2 |
| Builder seconds | 180.034 | 177.793 |
| Builder timed out | yes | no |
| Offline verification | pass | pass |
| Verification seconds | 12.661 | 12.306 |
| Critic seconds | 120.017 | 120.034 |
| Critic timed out | yes | yes |
| Completed critic verdict | none | none |
| Condition wall time, including stages | 313.844 | 311.233 |
| Builder compiler-command events | 7 | 6 |
| Critic compiler-command events | 3 | 5 |
| Submitted Lean lines | 195 | 174 |
| Builder input tokens | unknown | 196,665 |
| Cached input tokens, subset | unknown | 181,760 |
| Builder output tokens | unknown | 5,137 |
| Builder reasoning tokens, separately reported | unknown | 920 |
| Critic token usage | unknown | unknown |
| Monetary cost | unknown | unknown |
| Aristotle calls | 0 | 0 |

The incomplete sessions did not expose final usage totals. No missing usage or
cost is estimated. Cached input is not additional input, and reasoning/output
fields are not blindly added. Compiler-command events are not counts of proved
lemmas. Source length is not a quality metric. Setup, image building, and
connectivity costs are outside the per-condition times above.

The retrieved builder finished sooner, but the target remained incomplete and
both reviews timed out. This is **not** evidence of a verified efficiency gain.

## Retrieval and artifacts

The retrieved builder [reported opening](retrieved/passes/pass-001/retrieved/output/retrieval.md)
`pilot-general-lean-001`. It described intended use of the `abs_add_le` name,
positive-denominator advice, and stale-import advice. This documents its report,
not a measured causal effect. The automatic JSON's `retrieved_artifacts` remains
`unknown`; the Markdown retrieval record preserves the additional self-report.

Both conditions produced structured [JSON run records](artifacts/index.md),
Markdown summaries, prompts/transcripts, verification records, and per-pass
metrics. Both critics produced independent-check files/logs, but no `review.json`.
No candidate lessons were extracted from a completed rejection. No artifact was
approved, promoted, or transferred into this pair's retrieval snapshot.

## Reproducibility and limitations

Starting commit: `adbd5be23017f72e328742388ab7da063d17f5c3`.
Pipeline changes were uncommitted at launch; the [frozen manifest](frozen-manifest.json)
records hashes of the actual code, config, source, and memory used.
The missing runtime image was rebuilt before either condition started. Its
recorded ID is `sha256:8c6dc3e8d16fcf0da6174cc5ecd8ca1e0b964909520d2b79ca0b272ebaa1bad9`.
This repeats the protocol, not the old image bit-for-bit.

The paired comparison has one task, fixed order, shared library/page caches,
model sampling variation, and two unfinished reviews. It does not measure
generalization, plasticity, weight changes, critic accuracy, or cost savings.
The feedback loop was tested locally but was not exercised by these live agents.

The `check` command validates the new run's hashes, but its legacy display prints
`unknown` for nested bounded-run metrics. The measurements are present in
`comparison.json` and per-pass records; this report reads those actual values.

Task-owned containers and the proxy were removed. The main repository gate
passed after the run (8,036 build jobs plus placeholder/custom-axiom scans).
These build jobs are not 8,036 independent experimental tests.

## Next step — not executed

Before another pair, make the critic check whether the target theorem exists
and checkpoint its structured findings early. Separately pre-register an adequate
critic budget, equally for both conditions. Do not extend this run retroactively
or turn a critic timeout into a mathematical failure. Preserve this pair as-is.

## Evidence

- [Fixed config](experiment.json), [runtime identity](runtime.json), [preflight](preflight.json).
- [Machine comparison](comparison.json), [artifact index](artifacts/index.md).
- Stateless: [pass record](stateless/passes/pass-001/pass.json),
  [candidate](stateless/passes/pass-001/stateless/workspace/Research/Submission.lean),
  [verification](stateless/passes/pass-001/stateless/evaluation/verification.json),
  [critic metrics](stateless/passes/pass-001/stateless/review/metrics.json).
- Retrieved: [pass record](retrieved/passes/pass-001/pass.json),
  [candidate](retrieved/passes/pass-001/retrieved/workspace/Research/Submission.lean),
  [verification](retrieved/passes/pass-001/retrieved/evaluation/verification.json),
  [critic metrics](retrieved/passes/pass-001/retrieved/review/metrics.json).
