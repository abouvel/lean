"""Bounded builder/verifier/critic cycles; no cross-condition feedback transfer."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time
from datetime import datetime
from zoneinfo import ZoneInfo

from engine import Engine, CONFIG_FILES, ownership, save
from critic import read_review, review
from artifacts import write


def read(path):
    return json.loads(path.read_text())


def total(passes, role, key):
    values = [item.get(role, {}).get(key, "unknown") for item in passes]
    return sum(values) if values and all(type(value) in (int, float) for value in values) else "unknown"


def make_pass(parent, condition, number, previous=None, feedback=None):
    directory = parent.directory / condition / "passes" / f"pass-{number:03d}"
    directory.mkdir(parents=True, exist_ok=False)
    for key in ("inputs", "memory", "evaluator"):
        source = parent.directory / parent.config[key]
        for path in source.rglob("*"):
            if path.is_symlink():
                raise RuntimeError("Pass input symlink rejected")
        shutil.copytree(source, directory / parent.config[key])
    work = directory / condition / "workspace"
    (work / "Research").mkdir(parents=True)
    (work / ".lake").mkdir()
    for name in CONFIG_FILES:
        shutil.copyfile(directory / parent.config["evaluator"] / name, work / name)
    if previous:
        source = previous / condition / "workspace/Research"
        for path in source.rglob("*.lean"):
            if any(p.is_symlink() for p in (path, *path.parents)):
                raise RuntimeError("Candidate symlink rejected")
            target = work / "Research" / path.relative_to(source)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
    else:
        (work / "Research/Submission.lean").write_text("import Mathlib\n")
    output = directory / condition / "output"
    output.mkdir()
    ownership(work)
    ownership(output)
    save(directory / "preflight.json", {"inherited": {"exit_code": 0}})
    if feedback is not None:
        save(directory / "feedback/feedback.json", feedback)
    prompt = directory / parent.config["inputs"] / "PROMPT.txt"
    prompt.write_text(prompt.read_text() + f"\nController budget: pass {number}/{parent.config['max_passes']}; hard builder limit {parent.config['builder_seconds']} seconds. Original time estimates do not override this limit.\n")
    rubric = directory / parent.config["evaluator"] / "REVIEWER.txt"
    rubric.write_text(rubric.read_text() + f"\nController hard critic limit: {parent.config['critic_seconds']} seconds.\n")
    frozen = {str(path.relative_to(directory)): hashlib.sha256(path.read_bytes()).hexdigest()
              for folder in (parent.config["inputs"], parent.config["memory"], parent.config["evaluator"], "feedback")
              for path in (directory / folder).rglob("*") if path.is_file()}
    save(directory / "frozen-inputs.json", frozen)
    def guard():
        parent.guard()
        for name, expected in frozen.items():
            if hashlib.sha256((directory / name).read_bytes()).hexdigest() != expected:
                raise RuntimeError(f"Pass input changed: {name}")
    child = Engine(directory, parent.config, parent.lean, parent.packages, parent.auth, parent.guard)
    child.guard = guard
    child.conditions = (condition,)
    child.net, child.proxy = parent.net, parent.proxy
    return child


def execute(child, condition):
    root = child.directory / condition
    child.builders()
    builder = read(root / "output/metrics.json")
    if builder["exit_code"] != 0 and not builder.get("timed_out"):
        raise RuntimeError("Builder service/process failed (not a theorem failure)")
    child.evaluate()
    verification = read(root / "evaluation/verification.json")
    if verification.get("build_and_scans_exit_code") == 124:
        raise RuntimeError("Verification infrastructure timed out")
    result = {"builder": builder, "verification": verification, "critic": {}, "status": "formal_failed"}
    if verification["formal_gate_passed"]:
        review(child)
        result["critic"] = read(root / "review/metrics.json")
        if result["critic"]["exit_code"] != 0 or result["critic"].get("timed_out"):
            raise RuntimeError("Critic service/process failed")
        report = read_review(root / "review")
        result["report"] = report
        result["status"] = {"pass": "accepted", "fail": "critic_failed", "uncertain": "needs_human"}[report["overall_verdict"]]
    return result


def run_pair(engine, attempt=execute):
    comparison = {"schema_version": 1, "experiment_id": engine.directory.name,
                  "max_passes": engine.config["max_passes"], "conditions": {}}
    manifest = read(engine.directory / "frozen-manifest.json")
    for condition in engine.conditions:
        passes, previous, feedback = [], None, None
        started = time.monotonic()
        for number in range(1, engine.config["max_passes"] + 1):
            child = make_pass(engine, condition, number, previous, feedback)
            began = time.monotonic()
            try:
                result = attempt(child, condition)
            except (RuntimeError, OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
                # Preserve diagnostics locally, but don't manufacture proof feedback.
                result = {"status": "infrastructure_error", "error": str(error)}
                for label, relative in (("builder", "output/metrics.json"), ("critic", "review/metrics.json"),
                                        ("verification", "evaluation/verification.json")):
                    try:
                        result[label] = read(child.directory / condition / relative)
                    except (OSError, ValueError):
                        pass
            result.update(number=number, wall_time_seconds=time.monotonic() - began,
                          evidence=str(child.directory.relative_to(engine.directory)))
            save(child.directory / "pass.json", result)
            passes.append(result)
            if result["status"] not in ("formal_failed", "critic_failed"):
                break
            previous = child.directory
            report = result.get("report")
            feedback = {"schema_version": 1, "previous_pass": number,
                        "formal_gate_passed": result["verification"]["formal_gate_passed"],
                        "corrections": [{"requirement": item["requirement"], "correction": item["correction"]}
                                        for item in (report or {}).get("requirements", []) if item["verdict"] != "pass"],
                        "verification_log": (child.directory / condition / "evaluation/verification.log").read_text()}
        success = passes[-1]["status"] == "accepted"
        metrics = {"wall_time_seconds": time.monotonic() - started,
                   "passes_used": len(passes), "first_success_pass": len(passes) if success else None,
                   "builder_seconds": total(passes, "builder", "wall_time_seconds"),
                   "critic_seconds": total(passes, "critic", "wall_time_seconds"),
                   "compiler_command_events": total(passes, "builder", "compiler_command_events"),
                   "tokens": "unknown", "cost": "unknown", "aristotle_calls": 0,
                   "verification_calls": sum("verification" in item for item in passes),
                   "critic_calls": sum(bool(item.get("critic")) for item in passes),
                   "formal_failures": sum(item["status"] == "formal_failed" for item in passes),
                   "critic_rejections": sum(item["status"] == "critic_failed" for item in passes)}
        final_sources = list((child.directory / condition / "workspace/Research").rglob("*.lean"))
        metrics["final_source_lines"] = sum(len(path.read_text().splitlines()) for path in final_sources)
        for item in passes:
            log = engine.directory / item["evidence"] / condition / "output/retrieval.md"
            item["retrieval_record"] = str(log.relative_to(engine.directory)) if log.exists() else "unknown"
        for role in ("builder", "critic"):
            metrics[role + "_tokens"] = {}
            for key in ("input_tokens", "cached_input_tokens", "output_tokens", "reasoning_output_tokens"):
                values = [item.get(role, {}).get("token_usage", {}) for item in passes]
                numbers = [value.get(key, "unknown") if isinstance(value, dict) else "unknown" for value in values]
                metrics[role + "_tokens"][key] = sum(numbers) if all(type(n) is int for n in numbers) else "unknown"
        record = {"schema_version": 1, "artifact_id": datetime.now(ZoneInfo("America/New_York")).strftime("%Y-%m-%d") + "-" + condition,
                  "date": datetime.now(ZoneInfo("America/New_York")).date().isoformat(),
                  "experiment_id": engine.directory.name, "condition": condition,
                  "status": "verified" if success else "partial", "outcome": passes[-1]["status"], "success": success,
                  "task_id": engine.config["task_id"], "model": engine.config["model"],
                  "reasoning_effort": engine.config["reasoning_effort"], "starting_commit": manifest["starting_commit"],
                  "project": engine.config["task_id"], "memory_mode": condition,
                  "time_limit": {"max_passes": engine.config["max_passes"], "builder_seconds_per_pass": engine.config["builder_seconds"], "critic_seconds_per_pass": engine.config["critic_seconds"]},
                  "artifact_snapshot": manifest["hashes"], "retrieved_artifacts": "unknown" if condition == "retrieved" else [],
                  "verification_command": "bash pipeline/verify.sh", "passes": passes, "metrics": metrics,
                  "reuse": {"approved": False, "reason": "Review and remove target answers before freezing for a future run."}}
        record["candidate_lessons"] = [
            {"status": "unvalidated", "supporting_pass": item["number"], "requirement": requirement["requirement"],
             "evidence": requirement["evidence"], "proposed_correction": requirement["correction"]}
            for item in passes for requirement in item.get("report", {}).get("requirements", [])
            if requirement["verdict"] != "pass"]
        write(engine.directory, record)
        comparison["conditions"][condition] = record
        save(engine.directory / "comparison.json", comparison)
    return comparison
