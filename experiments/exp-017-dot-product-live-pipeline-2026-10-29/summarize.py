"""Record the completed paired proof run without modifying raw evidence."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REQUEST = "ok can you test this out with just the one proof from earlier"


def main():
    manifest_hash = hashlib.sha256((HERE / "batch-manifest.json").read_bytes()).hexdigest()
    results = {}
    table = ["| Metric | Stateless | Retrieved |", "| --- | ---: | ---: |"]
    for mode in ("stateless", "retrieved"):
        job = HERE / "runs" / ("dot-product-trial-001-" + mode)
        result = json.loads((job / "collected-result.json").read_text())
        record = result["record"]
        assert result["success"] and result["outcome"] == "accepted"
        assert len(record["passes"]) == 1
        proof_root = job / mode / "passes/pass-001" / mode
        for source in (job / "inputs/support/Research").rglob("*.lean"):
            candidate = proof_root / "workspace/Research" / source.relative_to(job / "inputs/support/Research")
            assert source.read_bytes() == candidate.read_bytes(), f"Supporting source changed: {candidate}"
        assert not list((job / "inputs").rglob("DotProduct.lean"))
        for condition in ("stateless", "retrieved"):
            assert (job / condition / "workspace/Research/Submission.lean").read_text() == "import Mathlib\n"
        results[mode] = record
        used = ["pilot-general-lean-001"] if mode == "retrieved" else []
        artifact_id = "2026-10-29-dot-product-end-to-end-" + mode
        text = f'''# Dot-product end-to-end proof run: {mode}

artifact_id: `{artifact_id}`
date: 2026-10-29
project: floating-point-dot-product-backward-error
status: verified
memory_mode: {mode}
retrieved_artifacts: {json.dumps(used)}
verification: job-specific trusted gate and independent critic passed; 72 pipeline tests and repository-wide `bash pipeline/verify.sh` passed (8,036 jobs, no placeholders/custom axioms).

experiment_id: `{HERE.name}`
condition: {mode}
task_id: `{record['task_id']}`
model: `{record['model']}`
reasoning_effort: `{record['reasoning_effort']}`
starting_commit: `{record['starting_commit']}`
artifact_snapshot: batch-manifest.json SHA-256 `{manifest_hash}`
time_limit: 2 passes, 180 builder seconds/pass, 240 critic seconds/pass, 2,400 whole-job seconds
verification_command: `bash pipeline/verify.sh`
success: true

## Request

{REQUEST}

## Target

Build the floating-point dot-product backward-error theorem from the natural-language specification and five prerequisite Lean modules. Prove that rounded multiplication followed by rounded tree addition equals the exact sum of leafwise perturbations of exact products, with bound gamma(depth+1,u), for arbitrary models and trees under only the requested smallness condition.

## Result

Accepted on the first pass. The trusted build and placeholder/custom-axiom scans passed. The independent critic passed all six catalog requirements with no extra assumptions or missing obligations.

## Decisions and reasoning

Both jobs began with the same `import Mathlib` submission and five identical prerequisite modules; no completed dot-product proof, prior candidate, prior report, or other condition's output was mounted. Source comparison after completion confirmed the five supplied modules were unchanged. The jobs ran with the same model, reasoning effort, tools, and budgets, stateless first.

'''
        if mode == "retrieved":
            text += "The builder's retrieval log records opening `pilot-general-lean-001`, with guidance about triangle inequalities, denominator positivity, and rebuilding imported modules. It pursued a direct depth induction. This is recorded external-context use, not evidence of changed model weights.\n\n"
        else:
            text += "The builder received no memory mount. It composed a multiplication perturbation lemma with the supplied rounded-sum perturbation theorem, then used the gamma step inequality.\n\n"
        text += f'''## What worked

The actual queue, archived coordinator and worker, preflight, resource leases, builder, verifier, critic, result validation, SQLite collection, and full-text search completed. No repair pass was needed.

## What failed

No acceptance gate failed in this fresh experiment. Earlier experiment exp-016 stopped after its accepted stateless job because a generated artifact index had mistakenly been frozen as input. That evidence is preserved. The planner now excludes job-local generated artifacts, and a regression test covers their mutation.

## Reusable observations

The two proof strategies both succeeded under equal budgets. One successful pair is an end-to-end functionality test; it cannot establish a general retrieval advantage. The retrieved proof loop took longer in this run.

## Evidence

- [Collected result](../runs/dot-product-trial-001-{mode}/collected-result.json)
- [Proof](../runs/dot-product-trial-001-{mode}/{mode}/passes/pass-001/{mode}/workspace/Research/Submission.lean)
- [Verification](../runs/dot-product-trial-001-{mode}/{mode}/passes/pass-001/{mode}/evaluation/verification.json)
- [Critic](../runs/dot-product-trial-001-{mode}/{mode}/passes/pass-001/{mode}/review/review.json)
- [Comparison](../comparison.json)

## Remaining limitations

One theorem and one successful pair were measured. Five proved prerequisites were supplied, so this is not a from-scratch formalization of all floating-point theory. The natural-language target was authoritative; the PDF was present only for launcher compatibility. API cost is unavailable. No human semantic sign-off or causal retrieval benefit is claimed.

## Metrics

- passes used: 1
- proof-loop wall time: {record['metrics']['wall_time_seconds']:.3f} seconds (excludes preflight, connectivity, queue wait, and cleanup)
- builder time: {record['metrics']['builder_seconds']} seconds
- critic time: {record['metrics']['critic_seconds']} seconds
- builder compiler-command events: {record['metrics']['compiler_command_events']}
- new submission lines: {len((proof_root / 'workspace/Research/Submission.lean').read_text().splitlines())}
- source lines including prerequisites: {record['metrics']['final_source_lines']}
- builder tokens: {json.dumps(record['metrics']['builder_tokens'])}
- critic tokens: {json.dumps(record['metrics']['critic_tokens'])}
- API cost: unknown
- distinct failed strategies: unknown
- Aristotle calls: 0
- semantic review passed: true
'''
        (HERE / "artifacts" / (artifact_id + ".md")).write_text(text)

    a, b = results["stateless"]["metrics"], results["retrieved"]["metrics"]
    table.extend([
        "| Accepted | yes | yes |",
        "| Passes used | 1 | 1 |",
        "| Lean + scans | pass | pass |",
        "| Critic requirements | 6/6 | 6/6 |",
        f"| Builder time | {a['builder_seconds']:.3f}s | {b['builder_seconds']:.3f}s |",
        f"| Critic time | {a['critic_seconds']:.3f}s | {b['critic_seconds']:.3f}s |",
        f"| Proof-loop wall time | {a['wall_time_seconds']:.3f}s | {b['wall_time_seconds']:.3f}s |",
    ])
    report = "# Live dot-product proof pipeline test\n\nBoth conditions built new valid proofs and were accepted on their first pass.\n\n" + "\n".join(table)
    report += '''

Times cover the proof loop and exclude preflight/connectivity, queue wait, and cleanup. The retrieved builder opened the generic frozen Lean artifact and recorded its influence; this single pair shows no speed or pass-count advantage from that memory.

This exercised the complete proof-building pipeline, including the actual archived coordinator and workers, trusted Lean verification, independent LLM criticism, result collection, completed-pair comparison, and full-text artifact search. Both jobs began without a completed dot-product proof. All five supplied prerequisite modules were unchanged at completion.

The live test exposed one infrastructure defect: generated job artifact indexes were initially included among frozen inputs. Experiment exp-016 preserves the interrupted run. After the fix and a regression test, the new experiment completed both conditions.

Final checks: 72 pipeline tests passed; the 8,036-job repository build and placeholder/custom-axiom scans passed; frozen-input checks, result search, and diff checks passed. API cost is unknown.
'''
    (HERE / "REPORT.md").write_text(report)
    index = "# Batch artifacts\n\n"
    for mode in ("retrieved", "stateless"):
        stem = "2026-10-29-dot-product-end-to-end-" + mode
        index += f"- `{stem}`; verified; project `floating-point-dot-product-backward-error`; tags: live, end-to-end, {mode}, dot-product; generated proof accepted on its first pass by Lean and the independent critic. [Summary]({stem}.md)\n"
    index += "- [Collected job results](jobs.md)\n"
    (HERE / "artifacts/index.md").write_text(index)


if __name__ == "__main__":
    main()
