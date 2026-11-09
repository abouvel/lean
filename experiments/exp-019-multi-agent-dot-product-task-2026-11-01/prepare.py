"""Preregister one revised multi-agent proof pair without target-answer leakage."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE=ROOT/"experiments/exp-015-dot-product-proof-task-2026-10-29"


def save(path,value):
    path.write_text(value if isinstance(value,str) else json.dumps(value,indent=2)+"\n")


def main():
    if (HERE/"frozen-manifest.json").exists(): raise RuntimeError("Already frozen")
    for folder in ("inputs","memory","evaluator"):
        shutil.copytree(BASE/folder,HERE/folder)
    save(HERE/"inputs/PROMPT.txt",'''Formalize the mathematics in /spec/source.txt.
Five proved prerequisite modules are provided under /spec/support/Research;
copy them unchanged into /workspace/Research. They cover the abstract rounding
model, gamma inequalities, binary trees, and rounded-sum analysis. No completed
dot-product theorem is supplied. Define exactProductTree, roundedProductTree,
and roundedDotProduct, and prove the full original componentwise backward-error
claim. The final theorem's name may vary. The algorithm is abstract real-valued
rounding under the supplied relative-error model; executable IEEE arithmetic is
not requested. An existential perturbation witness is the intended conclusion.
Follow your role-specific workflow. Formalizer proof skeletons may temporarily
use sorry, but the completed candidate must contain no placeholders or custom
axioms. Do not alter protected prerequisites or configuration. Use only local
Lean, Mathlib, and the approved memory snapshot when available. No Aristotle.
''')
    config=json.loads((BASE/"experiment.json").read_text())
    config.update(name=HERE.name,task_id="multi-agent-dot-product-roundtrip-pilot",
        revision={"schema_version":1,"mode":"calibration","seconds":{
            "planner":90,"formalizer":150,"prover":180,"translator":180,"judge":180},
            "construction_policy":"Define rounded leaf multiplication and rounded tree reduction, then prove gamma(depth+1,u) perturbations relative to exact products. The perturbation witness may be existential; executable IEEE arithmetic is not required."})
    save(HERE/"experiment.json",config)
    save(HERE/"protocol.json",{"experiment_id":HERE.name,"task_id":config["task_id"],
        "model":config["model"],"reasoning_effort":config["reasoning_effort"],
        "conditions":["stateless","retrieved"],"trials_per_condition":1,
        "role_budgets_seconds":config["revision"]["seconds"],"critic_seconds":config["critic_seconds"],
        "max_passes":2,"whole_job_seconds":3600,"verification_command":"bash pipeline/verify.sh",
        "acceptance_tests":["Both jobs produce validated result bundles through all role boundaries",
            "Accepted proofs pass Lean, protected-source checks, formalizer signature checks, and transitive axiom audit",
            "Accepted candidates receive agreeing independent direct and round-trip semantic passes",
            "Translator and judge receive neither research memory nor condition labels; translator receives no original task",
            "Source, mathematical prerequisites, models, and budgets remain identical across conditions; target proofs are absent from retrieval"],
        "human_review":"pending; this is an automated integration pilot, not expert-certified evaluator accuracy",
        "allowed_tools":["isolated local Lean and Mathlib","five approved prerequisites","frozen generic artifact only for retrieved production roles"]})
    save(HERE/"batch.json",{"schema_version":1,
        "limits":{"jobs":1,"model_calls":1,"lean_builds":1,"ram_gib":12,"job_seconds":3600},
        "tasks":[{"id":"dot-product","config":str((HERE/"experiment.json").relative_to(ROOT)),"trials":1,
            "memory_review":{"target_answer_excluded":True,"note":"Frozen pilot-general-lean-001 only: generic absolute-value, denominator, and stale-import guidance. No dot-product solution, prior candidate, evaluator output, or other-condition evidence is provided."}}]})
    commit=subprocess.run(["git","-C",str(ROOT),"rev-parse","HEAD"],check=True,capture_output=True,text=True).stdout.strip()
    files=[p for p in HERE.rglob("*") if p.is_file()]
    save(HERE/"frozen-manifest.json",{"experiment_id":HERE.name,"starting_commit":commit,
        "mode":"preregistered-multi-agent-task-template",
        "hashes":{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}})


if __name__ == "__main__": main()
