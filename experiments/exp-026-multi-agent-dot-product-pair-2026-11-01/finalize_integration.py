"""Summarize completed integration evidence; never change model reports."""
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent

def read(path):
    return json.loads(path.read_text())

comparison=read(HERE/"comparison.json")["pairs"]["dot-product-trial-001"]
rows=[]
proofs=[]
for condition in ("stateless","retrieved"):
    result=comparison[condition]
    assert result["success"] and result["outcome"]=="accepted",result
    job=HERE/"runs"/result["job_id"]
    record=read(job/"comparison.json")["conditions"][condition]
    final=record["passes"][-1]
    assert final["verification"]["formal_gate_passed"]
    assert final["verification"]["formal_audit"]["passed"]
    assert final["roundtrip"]["schema_version"]==2
    assert final["roundtrip"]["delivery_complete"] is True
    assert final["roundtrip"]["construction_complete"] is True
    assert final["roundtrip"]["overall_verdict"]=="pass"
    assert final["direct_report"]["overall_verdict"]=="pass"
    metrics=result["metrics"]
    assert all(metrics["roles"][role]["calls"]>=1 for role in ("planner","formalizer","prover","translator","judge"))
    rows.append(f"| {condition} | accepted | {metrics['passes_used']} | {metrics['wall_time_seconds']:.3f} | {metrics['total_model_seconds']:.3f} | {metrics['total_model_calls']} |")
    proof=job/final["evidence"]/condition/"workspace/Research/Submission.lean"
    proofs.append(f"[{condition} submission]({proof.relative_to(HERE).as_posix()})")

retrieved=HERE/"runs/dot-product-trial-001-retrieved/retrieved/passes/pass-001/retrieved/output/retrieval.json"
log=read(retrieved)
ids=sorted({item["artifact_id"] for item in log["opened_artifacts"]})
replacement="""Both frozen conditions completed all five isolated roles, the independent
direct critic, and trusted verification; both were accepted. The final axiom
audits found no unapproved axioms, changed protected files, or changed formalizer
declarations. Both semantic evaluators passed each final candidate.

| Condition | Outcome | Passes | Proof-loop wall seconds | Total model seconds | Model sessions |
| --- | --- | --- | --- | --- | --- |
"""+"\n".join(rows)+"\n\n"+", ".join(proofs)+".\n\n"+f"Retrieved artifact IDs actually opened: `{', '.join(ids)}`. Recorded decisions influenced: {len(log['decisions_influenced'])}. "
replacement+="See the [structured retrieval log](runs/dot-product-trial-001-retrieved/retrieved/passes/pass-001/retrieved/output/retrieval.json). Costs remain unknown. Wall time includes verification and local overhead; total model seconds sums model stages, including direct criticism.\n\n"
replacement+="See [comparison](comparison.json), [frozen plan](plan.json), and per-condition pass records for complete measured metrics.\n"
path=HERE/"REPORT.md"
text=path.read_text()
old="Pending completion of this experiment. See [frozen plan](plan.json) and\n[comparison](comparison.json) for current results."
assert old in text
path.write_text(text.replace(old,replacement))
print(replacement)
