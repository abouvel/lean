"""Freeze, verify, review, and score the dot-product critic benchmark."""
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
from critic import review
from critic_benchmark import score
from engine import Engine, mount, ownership, save


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def frozen_files(config):
    files = [HERE / name for name in
             ("protocol.json", "experiment.json", "prepare.py", "preflight.py", "run_benchmark.py")]
    for folder in ("inputs", "evaluator", "memory"):
        files.extend(path for path in (HERE / folder).rglob("*") if path.is_file())
    for case in config["conditions"]:
        files.extend(path for path in (HERE / case / "evaluation-workspace").rglob("*")
                     if path.is_file() and ".lake/build" not in str(path))
    files.extend(PIPELINE / name for name in
                 ("agent.py", "critic.py", "critic_benchmark.py", "engine.py", "verify.sh", "verify.py"))
    return files


def check_frozen():
    manifest = json.loads((HERE / "frozen-manifest.json").read_text())
    for relative, expected in manifest["hashes"].items():
        if digest(ROOT / relative) != expected:
            raise RuntimeError(f"Frozen input changed: {relative}")


def verify_cases(config, engine):
    for case in config["conditions"]:
        workspace, output = HERE / case / "evaluation-workspace", HERE / case / "evaluation"
        ownership(workspace)
        result = subprocess.run([
            *engine.container(case, workspace=workspace, output=output, offline=True),
            *mount(PIPELINE / "verify.sh", "/trusted/verify.sh", True),
            engine.image, "bash", "/trusted/verify.sh", "/workspace"
        ], text=True, capture_output=True, timeout=300)
        log = result.stdout + result.stderr
        (output / "verification.log").write_text(log)
        save(output / "verification.json", {"command": "bash pipeline/verify.sh",
             "build_and_scans_exit_code": result.returncode, "formal_gate_passed": result.returncode == 0})
        save(output / "container-exit.json", {"exit_code": result.returncode})
        if result.returncode:
            raise RuntimeError(f"Formal gate failed before critic launch: {case}\n{log}")


def write_benchmark_manifest(protocol):
    save(HERE / "benchmark.json", {"schema_version": 1, "catalog": "evaluator/requirements.json",
         "cases": [{"id": case["id"],
                    "report": f"{case['id']}/review/{case['expected_report']}",
                    "metrics": f"{case['id']}/review/metrics.json",
                    "expected_verdict": case["expected_verdict"],
                    "expected_defects": case["expected_defects"]} for case in protocol["cases"]]})


def main():
    config = json.loads((HERE / "experiment.json").read_text())
    protocol = json.loads((HERE / "protocol.json").read_text())
    if (HERE / "frozen-manifest.json").exists():
        raise RuntimeError("Experiment already frozen; never overwrite a live run")
    commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], check=True,
                            capture_output=True, text=True).stdout.strip()
    save(HERE / "frozen-manifest.json", {
        "experiment_id": HERE.name, "task_id": protocol["task_id"],
        "mode": "critic-only-held-out-theorem-family", "starting_commit": commit,
        "model": config["model"], "reasoning_effort": config["reasoning_effort"],
        "critic_time_limit_seconds": config["critic_seconds"],
        "verification_command": protocol["verification_command"], "frozen_unix": time.time(),
        "hashes": {str(path.relative_to(ROOT)): digest(path) for path in frozen_files(config)}
    })
    check_frozen()
    engine = Engine(HERE, config,
                    Path.home() / ".elan/toolchains/leanprover--lean4---v4.28.0",
                    ROOT / ".lake/packages",
                    Path(os.environ.get("RESEARCH_CODEX_AUTH", "/mnt/c/Users/austi/.codex/auth.json")),
                    check_frozen)
    verify_cases(config, engine)
    write_benchmark_manifest(protocol)
    try:
        review(engine)
    finally:
        engine.cleanup()
    result = score(HERE / "benchmark.json")
    save(HERE / "scores.json", result)
    print(json.dumps(result["summary"], indent=2))


if __name__ == "__main__":
    main()
