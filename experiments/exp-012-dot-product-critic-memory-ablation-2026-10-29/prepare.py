"""Create the preregistered paired critic-memory experiment without model calls."""
import importlib.util
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
SOURCE_EXPERIMENT = ROOT / "experiments/exp-011-dot-product-critic-2026-10-28"
SOURCE_PREPARE = SOURCE_EXPERIMENT / "prepare.py"
spec = importlib.util.spec_from_file_location("dot_product_cases", SOURCE_PREPARE)
source = importlib.util.module_from_spec(spec)
spec.loader.exec_module(source)

MEMORY_SOURCES = {
    "2026-10-27-critic-contract-canary": ROOT / "experiments/exp-005-critic-canary-2026-10-27/artifacts/2026-10-27-critic-contract-canary.md",
    "2026-10-28-critic-agent-stable-ids": ROOT / "experiments/exp-006-critic-benchmark-2026-10-28/artifacts/2026-10-28-critic-agent-stable-ids.md",
    "2026-10-28-five-case-live-critic": ROOT / "experiments/exp-009-critic-live-benchmark-2026-10-28/artifacts/2026-10-28-five-case-live-critic.md",
}


def main():
    protocol = json.loads((HERE / "protocol.json").read_text())
    base_cases = {case["id"]: case for case in protocol["base_cases"]}
    conditions = protocol["condition_order"]
    if set(protocol["artifact_snapshot_sources"]) != set(MEMORY_SOURCES):
        raise RuntimeError("Protocol and memory sources differ")

    inputs, evaluator, memory = HERE / "inputs", HERE / "evaluator", HERE / "memory"
    for directory in (inputs, evaluator, memory):
        directory.mkdir(exist_ok=False)
    (inputs / "source.txt").write_text(source.SOURCE)
    shutil.copyfile(source.PDF_SOURCE, inputs / "source.pdf")
    (evaluator / "REVIEWER.txt").write_text(source.RUBRIC)
    (evaluator / "requirements.json").write_text(json.dumps(source.CATALOG, indent=2) + "\n")

    index = ["# Approved frozen critic memory", "", "This snapshot predates the dot-product benchmark and contains no dot-product candidates, verdicts, or labels.", ""]
    for artifact_id, artifact_source in MEMORY_SOURCES.items():
        filename = artifact_id + ".md"
        shutil.copyfile(artifact_source, memory / filename)
        index.append(f"- `{artifact_id}`: [{filename}]({filename})")
    (memory / "index.md").write_text("\n".join(index) + "\n")

    candidates = source.candidate_sources()
    for condition in conditions:
        mode, case_id = condition.split("--", 1)
        if mode not in ("stateless", "retrieved") or case_id not in base_cases:
            raise RuntimeError(f"Invalid condition: {condition}")
        workspace = HERE / condition / "evaluation-workspace"
        (workspace / "Research").mkdir(parents=True)
        (workspace / ".lake/packages").mkdir(parents=True)
        for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
            shutil.copyfile(source.CONFIG_SOURCE / name, workspace / name)
        for relative in source.SUPPORT:
            target = workspace / "Research" / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / "lean/Research" / relative, target)
        (workspace / "Research.lean").write_text("import Research.Submission\n")
        (workspace / "Research/Submission.lean").write_text(candidates[case_id])
        (HERE / condition / "evaluation").mkdir()

    retrieved = [condition for condition in conditions if condition.startswith("retrieved--")]
    config = {
        "name": HERE.name,
        "task_id": protocol["task_id"],
        "model": protocol["model"],
        "reasoning_effort": protocol["reasoning_effort"],
        "conditions": conditions,
        "retrieved_conditions": retrieved,
        "critic_memory_enabled": True,
        "builder_seconds": 1,
        "critic_seconds": protocol["critic_time_limit_seconds"],
        "image": "research-proof-pilot-ready:2026-10-19",
        "inputs": "inputs",
        "memory": "memory",
        "evaluator": "evaluator",
        "aristotle_enabled": False,
        "resources": {"memory": "8g", "cpus": 2, "pids": 256},
        "verification_command": protocol["verification_command"],
    }
    (HERE / "experiment.json").write_text(json.dumps(config, indent=2) + "\n")


if __name__ == "__main__":
    main()
