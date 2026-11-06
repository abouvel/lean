# Separate roles and round-trip semantic evaluation

The revision is opt-in per experiment. Historical experiments keep their original
builder/verifier/critic path. The revised path runs planner, formalizer, prover,
trusted formal audit, direct critic, blind translator, and round-trip judge as
fresh sessions. The direct critic is retained during calibration; agreement is
an automated decision, not expert certification of evaluator accuracy.

## Configuration

```json
{
  "revision": {
    "schema_version": 1,
    "mode": "calibration",
    "seconds": {
      "planner": 90,
      "formalizer": 150,
      "prover": 180,
      "translator": 180,
      "judge": 180
    },
    "construction_policy": "Define the requested algorithm and prove its full original property."
  }
}
```

The normal `critic_seconds` limit still applies to the independent direct critic.
Use the same budgets and configuration for both artifact conditions. Whole-job
deadlines include every role, formal extraction, repairs, and resource waits.
Production mode is intentionally rejected until expert calibration is available.

## Interfaces and isolation

- `roles.py`: validated plan/statement handoffs and independent role containers.
- `role_agent.py`: one role session using the shared model runner.
- `ExtractContext.lean`: trusted elaboration-based project declaration extraction
  and one transitive axiom-dependency traversal.
- `formal_context.py`: protected source comparisons, source/environment
  fingerprints, formalizer/prover declaration comparison, and translation bundles.
- `roundtrip.py`: translation/judgment validation and conservative routing.
- `stages.py`: integrates the opt-in path without changing legacy runs.

Planner, formalizer, and prover get only the task, common prerequisites, same-job
handoffs/feedback, and the approved memory snapshot in the retrieved condition.
Each retrieved role must save a structured artifact-use log. Prover edits are
checked against the formalizer's elaborated theorem types and definition bodies;
new helper lemmas are allowed, silent statement/construction changes are not.

The translator runs in a separate sanitized workspace and sees only a formal
bundle: elaborated declarations, definition bodies, target identities, and
environment metadata. It does not receive original task text, source comments,
theorem proof terms, actor transcripts, research memory, previous verdicts, or
the condition label. The judge separately receives the original source, contract,
and validated translation, without candidate Lean code or the direct verdict.
Both evaluators are labeled `MEMORY_MODE=blind` in their runtime environment.

The extractor currently exports declarations from imported `Research*` modules.
It includes private and generated project definitions, rather than filtering by
public names. Mathematical primitives from Lean/Mathlib remain referenced by
their elaborated names; if more context is needed, the translator must report
`insufficient_context`. The current complete-bundle size ceiling is 300,000 JSON
characters; exceeding it is an explicit failure, not silent truncation.

## Trusted checks and decisions

The final formal gate requires a clean build and source scans, unchanged supplied
prerequisite files, unchanged formalizer declarations, and no transitive axioms
outside `propext`, `Classical.choice`, and `Quot.sound`. Temporary `sorryAx` is
permitted only for the formalizer's intermediate proof skeleton, never the final
proof. This does not ban classical reasoning inside a completed proof.

All translations and judgments must match the exact candidate hash. Translations
must cover every identified target and construction exactly once. Missing context
cannot produce a definitive pass. Judgment schema checks cover the full requirement
catalog and implication/relation consistency.

Translation schema 1 renders the actual formal statements. Judgment schema 2
records logical implication in both directions, `delivery_complete`,
`construction_complete`, and `missing_formal_steps`. Passing requires a complete
formal deliverable as well as mathematical implication. Supporting lemmas that
could be combined into the requested theorem are insufficient when that final
connection has not been proved in Lean. An explicit-answer task also cannot be
satisfied by existence or abstract choice alone. These checks are semantic LLM
judgments with deterministic schema validation, not kernel-certified equivalence.

During calibration:

| Direct critic | Round-trip judge | Controller |
| --- | --- | --- |
| pass | pass | accepted |
| fail | fail | repair if budget remains |
| disagreement or any uncertainty | any | human review |
| invalid report, stale hash, service failure, timeout | any | infrastructure error |

Raw reports are preserved separately from the controller's decision. Per-role
time, token measurements, and calls are saved in pass/job records; unknown data
remain unknown. The legacy `builder` metrics aggregate the three production roles.
`total_model_seconds` includes production, translation, judgment, and direct
criticism, but not verification, connectivity probes, or queue/setup overhead.
`total_model_calls` counts role/critic sessions, not individual API requests
within those sessions.

Human review of disagreements and randomly sampled passes/rejections is still
required before any claim about evaluator accuracy on naturally occurring tasks.
Controlled mutation cases test the interfaces and known defects, not universal
semantic reliability or a causal benefit from memory.

See the [implementation and live verification report](../experiments/exp-026-multi-agent-dot-product-pair-2026-11-01/REPORT.md)
for regression results, controlled evaluator calibration, preserved failures,
and the complete with/without-artifact dot-product integration pair.

## Controlled run and study scorecard

Start with the two frozen Algorithm 1 and Theorem 3.1 submissions. Both must
pass the offline formal gate. The direct critic and round-trip judge must
accept the complete submission and reject the one missing the original-input
link. This is a reviewer control using fixed Lean code, so it invokes no
proof-writing roles and reports no proof-production measurements.

```bash
python3 pipeline/binary_tree_control.py --name exp-my-binary-tree-control
python3 pipeline/batch.py plan \
  --spec pipeline/examples/roundtrip-study.json --name exp-my-roundtrip-study
# Launch the study after the control exits successfully.
python3 pipeline/batch.py run --experiment experiments/exp-my-roundtrip-study
```

The study specification has three trials per condition for each of dot product,
Horner evaluation, and forward differences, for 18 jobs. Each matched pair uses
the same task, model, role budgets, and prerequisite files. Only retrieved
production agents receive the approved snapshot.

The coordinator refreshes `scorecard.json` after each completed job. It records
the automated outcome, Lean and individual reviewer verdicts, round-trip
requirements, delivery and construction checks, repairs, timeout evidence,
job and proof-loop times, model and reasoning settings, role-level tokens, and
reported artifact use. Cached input is a subset of total input. Reviewers
report semantic verdicts and evidence rather than a numeric text-similarity
score. An unreviewed candidate has expert status `pending`.

To compare blind expert labels against the two model reviewers, write a JSON
object keyed by job ID. Each entry contains `candidate_hash` copied from the
scorecard and `verdict` equal to `pass`, `fail`, or `uncertain`. Generate a
separate copy of the scorecard with the expert labels and confusion counts:

```bash
python3 pipeline/metrics.py experiments/exp-my-roundtrip-study \
  --expert-labels reviewed-cases.json > reviewed-scorecard.json
```

The comparison reports false passes, false rejections, and uncertainty only
for cases with a decisive expert verdict. The automated outcomes and original
reports stay intact.
