"""Write experiment-local summaries without modifying frozen run evidence."""
import json
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parents[2]
DATE="2026-11-01"
specs={
    "exp-018-roundtrip-calibration-2026-11-01":("failed","Initial live translator output was mode 0600 and unreadable by the host. All six candidates passed formal preflight. No judge completed.","Export readable model outputs after atomic writes; keep mathematical inputs fixed in a fresh run."),
    "exp-020-roundtrip-calibration-2026-11-01":("failed","The first export-permission fix tried to chmod a host-owned directory and failed. No terminal judge verdict was obtained.","Normalize only container-owned files; a real UID-boundary canary passed before exp-021."),
    "exp-021-roundtrip-calibration-2026-11-01":("partial","Initial schema-1 round-trip calibration: 5/6 correct, one false pass (additions-only), no false rejection. The direct critic rejected that case; the controller stopped acceptance for human review.","Separate mathematical implication from completed Lean delivery. Preserve this baseline failure; use fresh schema-2 evaluation rather than changing labels."),
    "exp-022-construction-roundtrip-calibration-2026-11-01":("verified","Schema-2 construction calibration: 3/3 correct. Explicit expression accepted; existence-only and abstract choice rejected. No false pass or rejection on these controlled cases.","Construction policy is task-specific. Classical reasoning in a proof is allowed; abstract selection is insufficient when an explicit expression is required."),
    "exp-023-roundtrip-delivery-followup-2026-11-01":("verified","Development follow-up: 6/6 correct, no false passes or rejections. Reused blind translations from exp-021; only the schema-2 judge was rerun. This is not held-out accuracy.","The judge now records implication, delivery completeness, construction completeness, and missing formal steps separately."),
    "exp-024-multi-agent-dot-product-pair-2026-11-01":("failed","Both production conditions completed planner/formalizer/prover and built their Lean submission, but host augmentation of the verifier record failed due to container-owned mode-0644 outputs. This is an infrastructure failure, not a semantic rejection.","Make trusted verification exports host-writable. Preserve this frozen pair and rerun both conditions from the same original task state."),
    "exp-025-verifier-export-canary-2026-11-01":("verified","A real UID-1100 Docker verifier exported mode-0666 JSON/log files; the host successfully rewrote both. No model call was used. The shell build was a stub: this test makes no mathematical verification claim.","Exercise actual container/host ownership boundaries in addition to unit tests."),
}

def write(name,status,result,lesson):
    root=ROOT/"experiments"/name
    manifest=root/"frozen-manifest.json"
    if not manifest.exists() and (root/"batch-manifest.json").exists():
        manifest=root/"batch-manifest.json"
    config=json.loads((root/"experiment.json").read_text()) if (root/"experiment.json").exists() else {}
    if not config and (root/"plan.json").exists():
        plan=json.loads((root/"plan.json").read_text())
        config=json.loads((ROOT/plan["tasks"][0]["config"]).read_text())
    frozen=json.loads(manifest.read_text()) if manifest.exists() else {}
    commit=frozen.get("starting_commit","unknown")
    summary=root/"summary.json"
    names=[p for p in (root/"protocol.json",manifest,root/"plan.json",root/"comparison.json",root/"canary.py",root/"result.json",root/"FAILED.md") if p.exists()]
    evidence=", ".join(f"[{p.name}](../{p.name})" for p in names)
    if summary.exists(): evidence+=", [scores](../scores.json), [summary](../summary.json)"
    artifact=f"{DATE}-{name.split('-')[0]}-{name.split('-')[1]}-validation-summary"
    folder=root/"artifacts"
    folder.mkdir(exist_ok=True)
    text=f"""artifact_id: {artifact}
date: {DATE}
project: {name}
status: {status}
memory_mode: stateless
retrieved_artifacts: []
verification: See Evidence; repository gate `bash pipeline/verify.sh` also passed.
experiment_id: {name}
condition: stateless
task_id: {config.get('task_id','verifier-output-permission-canary')}
model: {config.get('model','not applicable; no model call')}
reasoning_effort: {config.get('reasoning_effort','not applicable')}
starting_commit: {commit}
artifact_snapshot: {manifest.name+' (includes dirty runtime hashes/archive)' if manifest.exists() else 'candidate-verify.py; no research memory'}
time_limit: {json.dumps(config.get('revision',{}).get('seconds','unknown'))}
verification_command: bash pipeline/verify.sh
success: {'true' if status=='verified' else 'false'}

## Request

Implement the saved revision and work until it can be verified.

## Target

Exercise isolated roles, Lean acceptance boundaries, and round-trip semantic evaluation.
Expected labels remain host-only; no prior research-memory artifact is exposed to evaluators.

## Result

{result}

## Decisions and reasoning

{lesson}

## What worked

Formal preflight, candidate fingerprinting, preserved raw outputs, and fail-closed routing
allow mechanical failures and semantic defects to be distinguished.

## What failed

{result if status!='verified' else 'No failure in the declared controlled acceptance test. Earlier failures remain in their original experiments.'}

## Reusable observations

{lesson} This record is raw experiment evidence, not a promoted validated lesson.

## Evidence

{evidence}.

## Remaining limitations

Expert semantic adjudication is pending. Controlled development cases and a single
dot-product pair do not establish general evaluator accuracy or a memory advantage.
The supplied model/reasoning settings and budgets are recorded in frozen configuration;
unknown measurements remain unknown.

## Metrics

Available per-role timing and token data remain in raw metrics and scores; cost: unknown.
Distinct failed mathematical strategies: unknown. Aristotle calls: 0.
"""
    (folder/f"{artifact}.md").write_text(text)
    (folder/"index.md").write_text(f"# Artifact index\n\n| ID | Status | Project | Tags | Summary | Path |\n| --- | --- | --- | --- | --- | --- |\n| {artifact} | {status} | {name} | round-trip, calibration, verification | {result} | [{artifact}]({artifact}.md) |\n")

if __name__=="__main__":
    for name,(status,result,lesson) in specs.items():
        write(name,status,result,lesson)
