"""Run the frozen positive and negative binary-tree reduction controls."""
import argparse
import hashlib
import json
import os
from contextlib import nullcontext
from pathlib import Path
import shutil
import subprocess
import time

from critic import completed_review, review
from engine import CONFIG_FILES, Engine, save
from formal_context import extract, source_hashes, translation_bundle
from metrics import summarize_job
from roundtrip import evaluate, route
from run import PIPELINE, ROOT, contained, prerequisites


def read(path):
    return json.loads(path.read_text())


def prepare(directory):
    plan_path = PIPELINE / "examples/binary-tree-roundtrip-control.json"
    plan = read(plan_path)
    old = contained(ROOT, plan["source"])
    baseline = contained(ROOT, plan["baseline"])
    config = read(baseline)
    config.update(name=directory.name, task_id="binary-tree-theorem-3.1-roundtrip-control",
                  conditions=[case["id"] for case in plan["cases"]])
    config["revision"]["construction_policy"] = (
        "Construct Algorithm 1 with offset pairing and unchanged carries, and deliver the "
        "full theorem on arbitrary nonempty original inputs and their occurrences."
    )
    directory.mkdir(parents=True)
    for name in ("inputs", "memory", "evaluator"):
        shutil.copytree(old / name, directory / name)
    for name in CONFIG_FILES:
        shutil.copyfile(old / "known-complete/evaluation-workspace" / name, directory / "evaluator" / name)
    shutil.copyfile(PIPELINE / "verify.sh", directory / "evaluator/verify.sh")
    for case in plan["cases"]:
        shutil.copytree(old / case["fixture"] / "evaluation-workspace/Research",
                        directory / case["id"] / "workspace/Research")
    save(directory / "experiment.json", config)
    save(directory / "protocol.json", {
        **plan, "model": config["model"], "reasoning_effort": config["reasoning_effort"],
        "role_seconds": config["revision"]["seconds"], "critic_seconds": config["critic_seconds"],
        "allowed_tools": "Isolated Lean, blind translator/judge, direct critic; no builder or research memory.",
        "verification_command": "bash pipeline/verify.sh",
        "acceptance_tests": [
            "Both fixed submissions pass the offline build, scans, and axiom audit.",
            "Both reviewers accept the complete original-input theorem.",
            "Both reviewers reject the compiling submission missing the original-input link.",
            "Both results expose measured time, roles, tokens, and requirement evidence; expert verdicts stay pending."
        ],
    })
    files = sorted(p for p in directory.rglob("*") if p.is_file())
    files.extend(p for p in PIPELINE.rglob("*") if p.is_file()
                 and p.suffix in {".py", ".sh", ".lean"} and "tests" not in p.parts)
    commit = subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip()
    manifest = {"starting_commit": commit,
                "hashes": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
    save(directory / "frozen-manifest.json", manifest)
    return plan, config, manifest


def run_case(engine, case):
    condition = case["id"]
    engine.conditions = (condition,)
    root = engine.directory / condition
    started = time.monotonic()
    engine.evaluate()
    verification = read(root / "evaluation/verification.json")
    if not verification["formal_gate_passed"]:
        raise RuntimeError("Controlled candidate failed Lean verification: " + condition)
    context, audit = extract(engine, condition, "final", evaluation=True)
    if not audit["passed"]:
        raise RuntimeError("Controlled candidate failed its dependency audit: " + condition)
    verification["formal_audit"] = audit
    save(root / "evaluation/verification.json", verification)
    review(engine)
    critic_metrics = read(root / "review/metrics.json")
    direct = completed_review(root / "review", critic_metrics)
    bundle = translation_bundle(context, case)
    rt, metrics = evaluate(engine, condition, bundle)
    if source_hashes(root / "evaluation-workspace") != context["sources"]:
        raise RuntimeError("Controlled candidate changed after evaluation")
    outcome, _ = route(direct, rt)
    accepted = outcome == "accepted"
    result = {"job_id": condition, "condition": "stateless", "outcome": outcome, "success": accepted,
              "record": {"task_id": engine.config["task_id"], "retrieved_artifacts": [],
                         "metrics": {"first_success_pass": 1 if accepted else None},
                         "passes": [{"number": 1, "verification": verification, "direct_report": direct,
                                     "roundtrip": rt, "roles": metrics, "critic": critic_metrics}]}}
    save(root / "result.json", result)
    score = summarize_job(result, root, time.monotonic() - started)
    expected_outcome = "accepted" if case["expected"] == "pass" else "critic_failed"
    score["expected_verdict"] = case["expected"]
    score["control_passed"] = outcome == expected_outcome and all(
        score[key] == case["expected"] for key in ("roundtrip", "direct_critic"))
    return score


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--name", required=True)
    args = parser.parse_args()
    directory = contained(ROOT / "experiments", args.name)
    plan, config, manifest = prepare(directory)

    def guard():
        for name, expected in manifest["hashes"].items():
            if hashlib.sha256(contained(ROOT, name).read_bytes()).hexdigest() != expected:
                raise RuntimeError("Frozen control input changed: " + name)

    lean = Path.home() / ".elan/toolchains/leanprover--lean4---v4.28.0"
    packages = ROOT / ".lake/packages"
    auth = Path(os.environ.get("RESEARCH_CODEX_AUTH", "/mnt/c/Users/austi/.codex/auth.json"))
    prerequisites(config, lean, packages, auth, online=True)
    engine = Engine(directory, config, lean, packages, auth, guard)
    engine.stage_gate = lambda stage: nullcontext()
    scores = []
    try:
        for case in plan["cases"]:
            print("RUN", case["id"], flush=True)
            score = run_case(engine, case)
            scores.append(score)
            save(directory / "scorecard.json", {"schema_version": 1, "jobs": scores})
            print("RESULT", case["id"], score["lean_verification"], score["direct_critic"],
                  score["roundtrip"], score["control_passed"], flush=True)
    finally:
        engine.cleanup()
    if not all(score["control_passed"] for score in scores):
        raise SystemExit("Binary-tree control did not meet its frozen acceptance tests.")
    print("BINARY_TREE_CONTROL_PASS", flush=True)


if __name__ == "__main__":
    main()
