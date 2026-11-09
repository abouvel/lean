"""Fresh, frozen judge-only follow-up; reuse blind translations, never verdicts as input."""
from contextlib import nullcontext
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "pipeline"))
from engine import Engine, save
from critic import completed_review, load_catalog
from formal_context import translation_bundle
from roles import launch
from roundtrip import JUDGE, validate_translation, validate_judgment, route

HERE = Path(__file__).resolve().parent

def prepare():
    prior = ROOT / "experiments/exp-021-roundtrip-calibration-2026-11-01"
    for name in ("inputs", "evaluator", "memory"):
        shutil.copytree(prior/name, HERE/name)
    config = json.loads((prior/"experiment.json").read_text())
    config["name"] = HERE.name
    save(HERE/"experiment.json", config)
    protocol = json.loads((prior/"protocol.json").read_text())
    protocol.update(experiment_id=HERE.name, purpose="Development follow-up, not held-out accuracy",
        reused="Frozen blind translations and direct reports from exp-021; only judge rerun",
        change="Schema 2 separates logical implication from completed formal delivery and construction",
        human_review="pending")
    save(HERE/"protocol.json", protocol)
    for case in config["conditions"]:
        dest = HERE/case/"reused"
        dest.mkdir(parents=True)
        shutil.copyfile(prior/case/"roles/translator/translation.json",dest/"translation.json")
        shutil.copyfile(prior/case/"formal-audit/dependencies/context.json",dest/"context.json")
        metrics=json.loads((prior/case/"review/metrics.json").read_text())
        save(dest/"direct.json",completed_review(prior/case/"review",metrics))

def run():
    if (HERE/"frozen-manifest.json").exists():
        raise RuntimeError("Do not rerun a frozen follow-up")
    files=[p for p in HERE.rglob("*") if p.is_file()]
    runtime=HERE/"runtime-source/pipeline"
    runtime.mkdir(parents=True)
    for p in (ROOT/"pipeline").iterdir():
        if p.suffix in (".py",".lean",".sh"):
            shutil.copyfile(p,runtime/p.name)
            files.append(p)
    hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    save(HERE/"frozen-manifest.json",{"hashes":hashes,"starting_commit":subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip()})
    def guard():
        for name,digest in hashes.items():
            if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest:
                raise RuntimeError("Frozen follow-up changed: "+name)
    config=json.loads((HERE/"experiment.json").read_text())
    engine=Engine(HERE,config,Path.home()/".elan/toolchains/leanprover--lean4---v4.28.0",ROOT/".lake/packages",
        Path(os.environ.get("RESEARCH_CODEX_AUTH","/mnt/c/Users/austi/.codex/auth.json")),guard)
    engine.stage_gate=lambda role:nullcontext()
    catalog=load_catalog(HERE/"evaluator/requirements.json")
    expected=json.loads((HERE/"protocol.json").read_text())["expected_verdicts"]
    # The expected labels and prior direct verdicts are never in the judge spec.
    shape={"overall_verdict":"pass|fail|uncertain","phase":"final","target_evidence":"string",
        "requirements":[{"requirement_id":"catalog ID","requirement":"string","evidence":"string",
            "verdict":"pass|fail|uncertain","defect_categories":[],"correction":"empty for pass; actionable for fail"}],
        "assumptions_added":[],"missing_obligations":[],"limitations":[]}
    scores={}
    try:
        for case in config["conditions"]:
            reuse=HERE/case/"reused"
            context=json.loads((reuse/"context.json").read_text())
            tr=json.loads((reuse/"translation.json").read_text())
            bundle=translation_bundle(context,{"targets":[x["name"] for x in tr["targets"]],
                "construction_names":[x["name"] for x in tr["constructions"]]})
            validate_translation(tr,bundle)
            out,metrics=launch(engine,case,"judge",JUDGE,payload={"translation.json":tr,
                "contract.json":{"requirements":catalog,"construction_policy":config["revision"].get("construction_policy","As required by source")},
                "report-contract.json":shape},files={"source.txt":HERE/"inputs/source.txt"})
            report=validate_judgment(out,bundle,tr,catalog)
            direct=json.loads((reuse/"direct.json").read_text())
            status,_=route(direct,report)
            scores[case]={"expected":expected[case],"roundtrip":report["overall_verdict"],
                "correct":report["overall_verdict"]==expected[case],"route":status,"metrics":metrics}
            save(HERE/"scores.json",scores)
            print("SCORED",case,report["overall_verdict"],status,flush=True)
    finally:
        engine.cleanup()
    summary={"cases":len(scores),"correct":sum(x["correct"] for x in scores.values()),
        "false_passes":sum(x["roundtrip"]=="pass" and x["expected"]=="fail" for x in scores.values()),
        "false_rejections":sum(x["roundtrip"]=="fail" and x["expected"]=="pass" for x in scores.values()),
        "human_review":"pending","evaluation_type":"development follow-up; reused translations"}
    save(HERE/"summary.json",summary)
    print(json.dumps(summary),flush=True)

if __name__=="__main__":
    {"prepare":prepare,"run":run}[sys.argv[1]]()
