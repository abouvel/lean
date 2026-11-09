"""Add compact experiment-local summaries; raw run records remain unchanged."""
import json
from pathlib import Path

root=Path(__file__).resolve().parent
index=root/"artifacts/index.md"
entries=[]
for condition in ("stateless","retrieved"):
    job=f"dot-product-trial-001-{condition}"
    record=json.loads((root/"runs"/job/"comparison.json").read_text())["conditions"][condition]
    assert record["success"]
    artifact=f"2026-11-01-exp-026-{condition}-integration"
    name=artifact+".md"
    fields={"artifact_id":artifact,"date":"2026-11-01","project":record["project"],
        "status":"verified","memory_mode":condition,"retrieved_artifacts":record["retrieved_artifacts"],
        "verification":"full candidate build/scans, elaborated axiom/protection audit, direct critic pass, round-trip pass",
        "experiment_id":root.name,"condition":condition,"task_id":record["task_id"],
        "model":record["model"],"reasoning_effort":record["reasoning_effort"],
        "starting_commit":record["starting_commit"],"artifact_snapshot":f"../runs/{job}/frozen-manifest.json; dirty runtime archived and hashed",
        "time_limit":record["time_limit"],"verification_command":"bash pipeline/verify.sh","success":True}
    metadata="\n".join(f"{k}: {json.dumps(v) if not isinstance(v,str) else v}" for k,v in fields.items())
    text=metadata+f"""

## Request

"implement this plan and work until you are able to verify it"

## Target

Define the rounded dot product and prove its full componentwise backward-error
theorem in the same abstract relative-rounding model, with the same five supplied
prerequisites and role budgets in both conditions. No locked final Lean statement
was supplied to production agents.

## Result

Accepted on pass 1. All five roles and the separate direct critic completed.
Final build/scans, transitive axiom audit, prerequisite protection, and declaration
preservation passed. Both semantic evaluators passed the exact fingerprinted candidate.

## Decisions and reasoning

Production roles communicate through explicit versioned files. Semantic evaluators
receive blinded inputs and no research memory. Logical implication alone cannot
credit an unproved final bridge. The controller requires both evaluators to agree
during calibration; uncertainty stops automatic acceptance.

## What worked

The complete frozen pipeline executed successfully with this memory condition.

## What failed

No failed pass in this run. Earlier failures remain in exp-018, exp-020, exp-021,
and exp-024; see the implementation report.

## Reusable observations

Keep mechanical proof checking and semantic correspondence separate. No lesson is
automatically promoted; controlled tests do not establish universal evaluator accuracy.

## Evidence

[Implementation report](../REPORT.md), [comparison](../comparison.json),
[full structured run record](../runs/{job}/artifacts/2026-11-01-{condition}.json).

## Remaining limitations

Expert semantic adjudication is pending. This single stateless-first pair does
not establish a memory advantage. Generic memory was opened in the retrieved
condition but no decisions were recorded as influenced. Costs remain unknown.

## Metrics

Proof-loop wall seconds: {record['metrics']['wall_time_seconds']:.3f}.
Total model-session seconds: {record['metrics']['total_model_seconds']:.3f}.
Model sessions: {record['metrics']['total_model_calls']}. Aristotle calls: 0.
Token measurements are preserved in the structured record. Distinct failed
mathematical strategies and isolated final proof size: unknown.
"""
    (root/"artifacts"/name).write_text(text)
    entries.append(f"| {artifact} | verified | {record['project']} | multi-agent, round-trip, {condition} | Full dot-product pipeline accepted on pass 1; expert adjudication pending. | [{name}]({name}) |")
index.write_text("# Batch artifacts\n\n| ID | Status | Project | Tags | Summary | Path |\n| --- | --- | --- | --- | --- | --- |\n"+"\n".join(entries)+"\n\n- [Collected job results](jobs.md)\n- [Implementation and verification report](../REPORT.md)\n")
