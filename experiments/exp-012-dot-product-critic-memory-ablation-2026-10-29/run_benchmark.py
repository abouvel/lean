"""Freeze, verify, run paired critics, validate retrieval, score, and compare."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PIPELINE = ROOT / "pipeline"
sys.path.insert(0, str(PIPELINE))
from critic import read_retrieval_log, review
from critic_benchmark import score
from engine import Engine, mount, ownership, save


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def frozen_files(config):
    files = [HERE / name for name in ("protocol.json", "experiment.json", "prepare.py", "preflight.py", "run_benchmark.py")]
    for folder in ("inputs", "evaluator", "memory"):
        files.extend(path for path in (HERE / folder).rglob("*") if path.is_file())
    for condition in config["conditions"]:
        files.extend(path for path in (HERE / condition / "evaluation-workspace").rglob("*")
                     if path.is_file() and ".lake/build" not in str(path))
    files.extend(PIPELINE / name for name in
                 ("agent.py", "critic.py", "critic_benchmark.py", "engine.py", "verify.sh", "verify.py"))
    files.append(ROOT / "experiments/exp-011-dot-product-critic-2026-10-28/prepare.py")
    return files


def check_frozen():
    manifest = json.loads((HERE / "frozen-manifest.json").read_text())
    for relative, expected in manifest["hashes"].items():
        if digest(ROOT / relative) != expected:
            raise RuntimeError(f"Frozen input changed: {relative}")


def clean_build_cache(engine, workspace):
    result = subprocess.run([
        "docker", "run", "--rm", "--network", "none",
        *mount(workspace, "/workspace"), engine.image,
        "bash", "-lc", "rm -rf /workspace/.lake/build",
    ], text=True, capture_output=True, timeout=60)
    if result.returncode:
        raise RuntimeError(f"Could not clean disposable Lean cache: {result.stderr}")


def verify_cases(config, engine):
    for condition in config["conditions"]:
        workspace = HERE / condition / "evaluation-workspace"
        output = HERE / condition / "evaluation"
        clean_build_cache(engine, workspace)
        ownership(workspace)
        result = subprocess.run([
            *engine.container(condition, workspace=workspace, output=output, offline=True),
            *mount(PIPELINE / "verify.sh", "/trusted/verify.sh", True),
            engine.image, "bash", "/trusted/verify.sh", "/workspace",
        ], text=True, capture_output=True, timeout=300)
        log = result.stdout + result.stderr
        (output / "verification.log").write_text(log)
        save(output / "verification.json", {
            "command": "bash pipeline/verify.sh",
            "build_and_scans_exit_code": result.returncode,
            "formal_gate_passed": result.returncode == 0,
        })
        save(output / "container-exit.json", {"exit_code": result.returncode})
        if result.returncode:
            raise RuntimeError(f"Formal gate failed before critic launch: {condition}\n{log}")


def case_for(condition, protocol):
    case_id = condition.split("--", 1)[1]
    return next(case for case in protocol["base_cases"] if case["id"] == case_id)


def write_benchmark_manifest(config, protocol):
    cases = []
    for condition in config["conditions"]:
        expected = case_for(condition, protocol)
        cases.append({
            "id": condition,
            "report": f"{condition}/review/{expected['expected_report']}",
            "metrics": f"{condition}/review/metrics.json",
            "expected_verdict": expected["expected_verdict"],
            "expected_defects": expected["expected_defects"],
        })
    save(HERE / "benchmark.json", {"schema_version": 1, "catalog": "evaluator/requirements.json", "cases": cases})


def validate_retrieval(config):
    logs = {}
    retrieved = set(config["retrieved_conditions"])
    for condition in config["conditions"]:
        output = HERE / condition / "review"
        log_path = output / "retrieval.json"
        if condition in retrieved:
            record = read_retrieval_log(output)
            if not record["opened_artifacts"]:
                raise RuntimeError(f"Retrieved critic opened no approved artifact: {condition}")
            logs[condition] = record
        elif log_path.exists():
            raise RuntimeError(f"Stateless critic unexpectedly wrote a retrieval log: {condition}")
    save(HERE / "retrieval-logs.json", logs)


def summarize_mode(mode, scored):
    cases = [case for case in scored["cases"] if case["id"].startswith(mode + "--")]
    return {
        "total_cases": len(cases),
        "verdicts_correct": sum(case.get("verdict_correct", False) for case in cases),
        "false_passes": sum(case.get("false_pass", False) for case in cases),
        "false_rejections": sum(case.get("false_rejection", False) for case in cases),
        "invalid_reports": sum(case.get("status") == "invalid_report" for case in cases),
        "timeouts": sum(case.get("status") == "timeout" for case in cases),
        "expected_defects_found": sum(len(case["expected_defects"]) if case.get("expected_defects_found") else 0 for case in cases),
        "expected_defects_total": sum(len(case["expected_defects"]) for case in cases),
        "critic_wall_time_seconds": round(sum(json.loads((HERE / case["id"] / "review/metrics.json").read_text())["wall_time_seconds"] for case in cases), 3),
    }


def main():
    config = json.loads((HERE / "experiment.json").read_text())
    protocol = json.loads((HERE / "protocol.json").read_text())
    if (HERE / "frozen-manifest.json").exists():
        raise RuntimeError("Experiment already frozen; never overwrite a live run")
    commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], check=True,
                            capture_output=True, text=True).stdout.strip()
    save(HERE / "frozen-manifest.json", {
        "experiment_id": HERE.name,
        "task_id": protocol["task_id"],
        "mode": "paired-critic-memory-ablation",
        "starting_commit": commit,
        "model": config["model"],
        "reasoning_effort": config["reasoning_effort"],
        "critic_time_limit_seconds": config["critic_seconds"],
        "verification_command": protocol["verification_command"],
        "condition_order": config["conditions"],
        "frozen_unix": time.time(),
        "hashes": {str(path.relative_to(ROOT)): digest(path) for path in frozen_files(config)},
    })
    check_frozen()
    engine = Engine(HERE, config,
                    Path.home() / ".elan/toolchains/leanprover--lean4---v4.28.0",
                    ROOT / ".lake/packages",
                    Path(os.environ.get("RESEARCH_CODEX_AUTH", "/mnt/c/Users/austi/.codex/auth.json")),
                    check_frozen)
    verify_cases(config, engine)
    write_benchmark_manifest(config, protocol)
    try:
        review(engine)
    finally:
        engine.cleanup()
    validate_retrieval(config)
    result = score(HERE / "benchmark.json")
    save(HERE / "scores.json", result)
    comparison = {mode: summarize_mode(mode, result) for mode in ("stateless", "retrieved")}
    save(HERE / "comparison.json", comparison)
    print(json.dumps(comparison, indent=2))


if __name__ == "__main__":
    main()
