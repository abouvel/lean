"""Replay round-trip reviews blocked by the former definition-only handoff."""
import argparse
from contextlib import nullcontext
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

from critic import completed_review
from engine import CONFIG_FILES, Engine, save
from formal_context import fingerprint, source_hashes, translation_bundle
from metrics import summarize_job
from resources import atomic_json
from roles import handoff
from roundtrip import evaluate, route
from run import PIPELINE, ROOT, contained, prerequisites

OLD_ERROR = "Construction is absent or is not a definition: "


def read(path):
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare(source, destination):
    if destination.exists():
        raise FileExistsError("Replay experiment already exists")
    cases = []
    for job in read(source / "plan.json")["jobs"]:
        run = contained(source, job["directory"])
        result = read(run / "collected-result.json")
        if result["outcome"] != "infrastructure_error":
            continue
        attempt = result["record"]["passes"][-1]
        if not attempt.get("error", "").startswith(OLD_ERROR):
            continue
        previous = contained(run, attempt["evidence"])
        work = previous / job["condition"]
        verification = attempt["verification"]
        audit = verification["formal_audit"]
        context = read(work / "formal-audit/final/context.json")
        candidate = context["candidate_hash"]
        if (not verification["formal_gate_passed"] or not audit["passed"]
                or audit["candidate_hash"] != candidate
                or fingerprint({k: v for k, v in context.items() if k != "candidate_hash"}) != candidate
                or source_hashes(work / "evaluation-workspace") != context["sources"]
                or source_hashes(work / "workspace") != context["sources"]):
            raise ValueError("Original Lean verification or source fingerprint mismatch: " + job["job_id"])
        statement = handoff(work / "roles/formalizer", "formalizer")
        if statement != attempt["builder"]["statement"]:
            raise ValueError("Original formalizer handoff changed: " + job["job_id"])
        bundle = translation_bundle(context, statement)
        metrics = read(work / "review/metrics.json")
        direct = completed_review(work / "review", metrics)
        config = read(run / "experiment.json")
        case = f"replay-{destination.name.split('-')[1]}-{len(cases) + 1:02d}"
        config.update(conditions=["stateless"], inputs="inputs", evaluator="evaluator")
        files = {"inputs/source.txt": previous / "inputs/source.txt"}
        files.update({f"evaluator/{name}": previous / "evaluator" / name
                      for name in (*CONFIG_FILES, "requirements.json")})
        if digest(files["evaluator/requirements.json"]) != digest(work / "reviewer-spec/requirements.json"):
            raise ValueError("Original direct-critic rubric differs: " + job["job_id"])
        if digest(files["inputs/source.txt"]) != digest(work / "reviewer-spec/source.txt"):
            raise ValueError("Original direct-critic source differs: " + job["job_id"])
        cases.append((case, job, config, files, bundle, verification, direct, metrics, attempt["error"]))
    if not cases:
        raise ValueError("No eligible archived handoff failures")
    destination.mkdir(parents=True)
    index = []
    for case, job, config, files, bundle, verification, direct, metrics, error in cases:
        path = destination / case
        for relative, original in files.items():
            target = path / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(original, target)
        save(path / "experiment.json", config)
        save(path / "formal-bundle.json", bundle)
        save(path / "prior-verification.json", verification)
        save(path / "prior-direct-critic.json", direct)
        save(path / "prior-direct-metrics.json", metrics)
        index.append({"case": case, "job_id": job["job_id"], "condition": job["condition"],
                      "task_id": job["task_id"], "original_failure": error,
                      "candidate_hash": bundle["candidate_hash"]})
    save(destination / "protocol.json", {
        "source_experiment": source.name, "cases": index,
        "verification": "Reuse the original trusted Lean build and audit after verifying its fingerprint and source hashes.",
        "evaluation": "Reuse each valid original direct-critic report. Run fresh isolated blind translation and round-trip judgment.",
        "production_roles_invoked": False, "expert_verdict": "pending",
    })
    files = [path for path in destination.rglob("*") if path.is_file()]
    files += [path for path in PIPELINE.rglob("*") if path.is_file()
              and path.suffix in {".py", ".sh", ".lean"} and "tests" not in path.parts]
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    save(destination / "frozen-manifest.json", {
        "starting_commit": commit, "hashes": {str(path.relative_to(ROOT)): digest(path) for path in files},
    })
    print(f"PREPARED {len(index)} cases", flush=True)


def run(destination):
    protocol = read(destination / "protocol.json")
    manifest = read(destination / "frozen-manifest.json")

    def guard():
        for name, expected in manifest["hashes"].items():
            if digest(contained(ROOT, name)) != expected:
                raise RuntimeError("Frozen replay input changed: " + name)

    guard()
    lean = Path.home() / ".elan/toolchains/leanprover--lean4---v4.28.0"
    packages = ROOT / ".lake/packages"
    auth = Path(os.environ.get("RESEARCH_CODEX_AUTH", "/mnt/c/Users/austi/.codex/auth.json"))
    jobs = []
    for item in protocol["cases"]:
        path = destination / item["case"]
        config = read(path / "experiment.json")
        if not jobs:
            prerequisites(config, lean, packages, auth, online=True)
        if (path / "result.json").exists():
            raise FileExistsError("Replay already attempted: " + item["case"])
        engine = Engine(path, config, lean, packages, auth, guard)
        engine.stage_gate = lambda stage: nullcontext()
        previous = read(path / "prior-verification.json")
        direct = read(path / "prior-direct-critic.json")
        details = {"number": 1, "verification": previous, "direct_report": direct}
        print("RUN", item["job_id"], flush=True)
        started = time.monotonic()
        try:
            rt, metrics = evaluate(engine, "stateless", read(path / "formal-bundle.json"))
            outcome, combined = route(direct, rt)
            details.update(roundtrip=rt, report=combined, roles=metrics)
        except (OSError, RuntimeError, ValueError, KeyError, subprocess.SubprocessError) as error:
            outcome = "infrastructure_error"
            details["error"] = str(error)
            details["roles"] = {}
            for role in ("translator", "judge"):
                metrics_path = path / "stateless/roles" / role / "metrics.json"
                if metrics_path.is_file():
                    details["roles"][role] = read(metrics_path)
        finally:
            engine.cleanup()
        result = {"job_id": item["job_id"], "condition": item["condition"], "outcome": outcome,
                  "success": outcome == "accepted",
                  "record": {"task_id": item["task_id"], "passes": [details]}}
        save(path / "result.json", result)
        score = summarize_job(result, path, time.monotonic() - started)
        score.update(source_case=item["case"], reused_lean_verification=True, reused_direct_critic=True,
                     original_outcome="infrastructure_error", error=details.get("error"))
        jobs.append(score)
        atomic_json(destination / "scorecard.json", {"schema_version": 1, "jobs": jobs})
        print("RESULT", item["job_id"], score["direct_critic"], score["roundtrip"], outcome, flush=True)
    print(f"FINISHED {len(jobs)} replay cases", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("prepare", "run"))
    parser.add_argument("--name", required=True)
    parser.add_argument("--source")
    args = parser.parse_args()
    destination = contained(ROOT / "experiments", args.name)
    if args.action == "prepare":
        if not args.source:
            parser.error("prepare requires --source")
        prepare(contained(ROOT / "experiments", args.source), destination)
    else:
        run(destination)


if __name__ == "__main__":
    main()
