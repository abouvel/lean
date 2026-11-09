"""Run formal preflight, then freeze before making any evaluator calls."""
from contextlib import nullcontext
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "pipeline"))
from engine import Engine, save
from critic import completed_review, review
from formal_context import extract, source_hashes, translation_bundle
from roundtrip import evaluate, route


def guard():
    manifest = HERE / "frozen-manifest.json"
    if manifest.exists():
        for name, expected in json.loads(manifest.read_text())["hashes"].items():
            if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != expected:
                raise RuntimeError("Frozen calibration input changed: " + name)


def engine():
    config = json.loads((HERE / "experiment.json").read_text())
    value = Engine(HERE, config, Path.home()/".elan/toolchains/leanprover--lean4---v4.28.0",
        ROOT/".lake/packages", Path(os.environ.get("RESEARCH_CODEX_AUTH", "/mnt/c/Users/austi/.codex/auth.json")), guard)
    value.stage_gate = lambda stage: nullcontext()
    return value


def preflight():
    value = engine()
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "Research.lean"):
        dest = HERE/"evaluator"/name
        if not dest.exists():
            shutil.copyfile(HERE/"known-complete/workspace"/name,dest)
    if not (HERE/"evaluator/verify.sh").exists():
        shutil.copyfile(ROOT/"pipeline/verify.sh",HERE/"evaluator/verify.sh")
    for case in value.conditions:
        incomplete = HERE/case/"evaluation-workspace"
        if incomplete.exists() and not (HERE/case/"evaluation/verification.json").exists():
            shutil.move(incomplete,HERE/case/"setup-incomplete-workspace")
    value.evaluate()
    for case in value.conditions:
        verified = json.loads((HERE/case/"evaluation/verification.json").read_text())
        if not verified["formal_gate_passed"]: raise RuntimeError("Formal gate failed: " + case)
        context, audit = extract(value, case, "calibration", evaluation=True)
        if not audit["passed"]: raise RuntimeError("Trusted axiom/protection gate failed: " + case)
        print("FORMAL_CONTEXT_PASS",case,len(context["declarations"]),flush=True)


def freeze():
    if (HERE/"frozen-manifest.json").exists(): raise RuntimeError("Never overwrite a frozen calibration")
    files = [HERE/name for name in ("experiment.json","protocol.json","prepare.py","run_calibration.py")]
    for folder in ("inputs","memory","evaluator"):
        files.extend(p for p in (HERE/folder).rglob("*") if p.is_file())
    for case in engine().conditions:
        files.extend(p for p in (HERE/case/"workspace").rglob("*") if p.is_file() and ".lake" not in p.parts)
        files += [HERE/case/"formal-audit/dependencies/context.json", HERE/case/"formal-audit/dependencies/audit.json"]
    runtime = HERE/"runtime-source/pipeline"
    runtime.mkdir(parents=True)
    for p in (ROOT/"pipeline").iterdir():
        if p.suffix in (".py",".sh",".lean"):
            shutil.copyfile(p,runtime/p.name)
            files.append(p)
    commit = subprocess.run(["git","-C",str(ROOT),"rev-parse","HEAD"],check=True,capture_output=True,text=True).stdout.strip()
    save(HERE/"frozen-manifest.json",{"experiment_id":HERE.name,"starting_commit":commit,
        "hashes":{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}})


def run():
    freeze()
    value = engine()
    expected = json.loads((HERE/"protocol.json").read_text())["expected_verdicts"]
    outcomes = {}
    try:
        for case in value.conditions:
            context = json.loads((HERE/case/"formal-audit/dependencies/context.json").read_text())
            if source_hashes(HERE/case/"evaluation-workspace") != context["sources"]:
                raise RuntimeError("Calibration source changed")
            targets = [x["name"] for x in context["declarations"] if x["kind"]=="theorem" and x["module"]=="Research.Submission" and not x["name"].startswith("_")]
            names = [x["name"] for x in context["declarations"] if x["kind"]=="definition" and x["name"].split(".")[-1] in ("exactProductTree","roundedProductTree","roundedDotProduct")]
            named=json.loads((HERE/"protocol.json").read_text()).get("construction_names")
            if named is not None:
                names=[x["name"] for x in context["declarations"] if x["kind"]=="definition" and x["name"] in named]
            bundle = translation_bundle(context,{"targets":targets,"construction_names":names})
            report, metrics = evaluate(value,case,bundle)
            direct_engine = engine()
            direct_engine.conditions = (case,)
            review(direct_engine)
            direct_metrics = json.loads((HERE/case/"review/metrics.json").read_text())
            direct = completed_review(HERE/case/"review",direct_metrics)
            status,_ = route(direct,report)
            outcomes[case] = {"expected":expected[case],"roundtrip":report["overall_verdict"],
                "direct":direct["overall_verdict"],"correct":report["overall_verdict"]==expected[case],
                "route":status,"role_metrics":metrics,"critic_metrics":direct_metrics}
            save(HERE/"scores.json",outcomes)
            print("SCORED",case,json.dumps({k:v for k,v in outcomes[case].items() if not k.endswith("metrics")}),flush=True)
    finally:
        value.cleanup()
    summary={"cases":len(outcomes),"roundtrip_correct":sum(x["correct"] for x in outcomes.values()),
        "false_passes":sum(x["roundtrip"]=="pass" and x["expected"]=="fail" for x in outcomes.values()),
        "false_rejections":sum(x["roundtrip"]=="fail" and x["expected"]=="pass" for x in outcomes.values()),
        "uncertain":sum(x["roundtrip"]=="uncertain" for x in outcomes.values()),
        "human_review":"pending"}
    save(HERE/"summary.json",summary)
    print(json.dumps(summary,indent=2))


def refresh():
    value = engine()
    for case in value.conditions:
        context,audit=extract(value,case,"dependencies",evaluation=True)
        if not audit["passed"]: raise RuntimeError("Trusted audit failed: "+case)
        print("DEPENDENCY_CONTEXT_PASS",case,len(context["declarations"]),flush=True)


if __name__ == "__main__":
    {"preflight":preflight,"refresh":refresh,"run":run}[sys.argv[1]]()
