"""Run a self-contained experiment with shared Docker/Lean machinery."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

from engine import CONFIG_FILES, Engine, ownership, save
from critic import require_pass, review

ROOT = Path(__file__).resolve().parents[1]
PIPELINE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def contained(base, name):
    raw = base / name
    path = raw.resolve()
    if not path.is_relative_to(base.resolve()) or any(p.is_symlink() for p in (raw, *raw.parents)):
        raise RuntimeError(f"Unsafe path: {name}")
    return path


def validate_name(name):
    if not re.fullmatch(r"[a-z0-9][a-z0-9-]{0,63}", name):
        raise RuntimeError("name must be 1–64 lowercase letters, numbers or hyphens")


def load_config(path):
    path = path.resolve()
    if not path.is_relative_to(ROOT / "experiments"):
        raise RuntimeError("Config must be inside experiments/.")
    config = json.loads(path.read_text())
    if config["conditions"] != ["stateless", "retrieved"]:
        raise RuntimeError("This runner supports the fixed stateless/retrieved pair.")
    if config.get("aristotle_enabled", False):
        raise RuntimeError("Aristotle fallback is not implemented; keep it disabled in both conditions.")
    if "max_passes" in config:
        for key in ("max_passes", "builder_seconds", "critic_seconds"):
            if type(config[key]) is not int or config[key] <= 0:
                raise RuntimeError(f"{key} must be a positive integer")
    directories = [contained(path.parent, config[key]) for key in ("inputs", "memory", "evaluator")]
    for i, directory in enumerate(directories):
        if not directory.is_dir():
            raise RuntimeError(f"Missing input directory: {directory}")
        for other in directories[i + 1:]:
            if directory.is_relative_to(other) or other.is_relative_to(directory):
                raise RuntimeError("Builder inputs, memory, and evaluator directories must be separate.")
    return path.parent, config


def checked_record(directory, relocation=None):
    """Historical paths are mapped, never rewritten in their frozen manifest.

    Original pipeline bytes are checked in Git, not confused with the refactored
    active implementation. New runs hash the active implementation directly.
    """
    path = directory / "frozen-manifest.json"
    if relocation:
        expected = relocation["manifests"].get(str(path.relative_to(ROOT)))
        if expected and digest(path) != expected:
            raise RuntimeError(f"Historical manifest changed: {path}")
    manifest = json.loads(path.read_text())
    for name, expected in manifest["hashes"].items():
        if relocation and name.startswith("pipeline/isolated_experiment/"):
            original = subprocess.run(
                ["git", "-C", str(ROOT), "show", relocation["historical_code_commit"] + ":" + name],
                check=True, capture_output=True, timeout=10).stdout
            actual = hashlib.sha256(original).hexdigest()
        else:
            mapped = name
            if relocation:
                for old, new in sorted(relocation["paths"].items(), key=lambda pair: -len(pair[0])):
                    if name == old or name.startswith(old + "/"):
                        mapped = new + name[len(old):]
                        break
            actual = digest(contained(ROOT, mapped))
        if actual != expected:
            raise RuntimeError(f"Frozen input changed: {name}")
    return manifest


def check_experiment(directory, config):
    relocation_path = directory / config["relocation"] if config.get("relocation") else None
    relocation = json.loads(relocation_path.read_text()) if relocation_path else None
    for record in config.get("historical_records", ["."]):
        checked_record(contained(directory, record), relocation)
    return checked_record(directory, relocation)


def initialize(target, source, config, replay):
    target.mkdir(parents=True, exist_ok=False)
    current = dict(config)
    for key in ("relocation", "historical_records"):
        current.pop(key, None)
    current["name"] = target.name
    for key in ("inputs", "memory", "evaluator"):
        original = contained(source, config[key])
        for file in original.rglob("*"):
            contained(original, file.relative_to(original))
        shutil.copytree(original, contained(target, config[key]))
    for condition in config["conditions"]:
        work = target / condition / "workspace"
        (work / "Research").mkdir(parents=True)
        (work / ".lake").mkdir()
        for name in CONFIG_FILES:
            shutil.copyfile(target / config["evaluator"] / name, work / name)
        if replay:
            actor = source / condition / "workspace/Research"
            for file in actor.rglob("*.lean"):
                contained(actor, file.relative_to(actor))
                dest = work / "Research" / file.relative_to(actor)
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(file, dest)
        else:
            (work / "Research/Submission.lean").write_text("import Mathlib\n")
        out = target / condition / "output"
        out.mkdir()
        ownership(work)
        ownership(out)
    (target / "artifacts").mkdir()
    save(target / "artifacts/index.md", "# Run artifacts\n\n"
         "Add run summaries here after evaluation. Do not expose them to either builder.\n")
    save(target / "experiment.json", current)
    files = [p for key in ("inputs", "memory", "evaluator")
             for p in (target / current[key]).rglob("*") if p.is_file()]
    files += [target / "experiment.json"]
    files += [p for p in PIPELINE.rglob("*") if p.is_file() and
              (p.suffix in (".py", ".sh") or p.name.startswith("Dockerfile")) and
              "__pycache__" not in p.parts and "tests" not in p.parts]
    if replay:
        files += list(target.glob("*/workspace/Research/**/*.lean"))
    commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"],
                            check=True, capture_output=True, text=True).stdout.strip()
    save(target / "frozen-manifest.json", {
        "experiment_id": target.name, "task_id": current["task_id"],
        "mode": "offline-replay" if replay else "fresh-pair",
        "starting_commit": commit, "model": current["model"],
        "reasoning_effort": current["reasoning_effort"],
        "condition_order": current["conditions"],
        "builder_time_limit_seconds": current["builder_seconds"],
        "reviewer_time_limit_seconds": current["critic_seconds"],
        "verification_command": "bash pipeline/verify.sh",
        "source_experiment": str(source.relative_to(ROOT)),
        "source_manifest_sha256": digest(source / "frozen-manifest.json"),
        "frozen_unix": time.time(),
        "hashes": {str(p.relative_to(ROOT)): digest(p) for p in files}})
    save(target / "README.md", "# " + target.name + "\n\n"
         + ("Offline rebuild of saved submissions; no agents or semantic critics rerun.\n" if replay else
            "Fresh paired experiment. Builders receive only inputs and optional frozen memory, not prior solutions.\n")
         + "\nSee experiment.json, comparison.json, and each condition's output/evaluation/review folders.\n")
    return current


def prerequisites(config, lean, packages, auth, online):
    if sys.platform != "linux":
        raise RuntimeError("Run inside WSL/Linux, not PowerShell.")
    for path in (lean / "bin/lean", packages / "mathlib"):
        if not path.exists():
            raise RuntimeError(f"Missing dependency: {path}")
    if online and not auth.is_file():
        raise RuntimeError("Missing authentication file; use --auth, outside this repository.")
    try:
        subprocess.run(["docker", "info"], check=True, capture_output=True, timeout=20)
        subprocess.run(["docker", "image", "inspect", config["image"]],
                       check=True, capture_output=True, timeout=20)
    except subprocess.SubprocessError as error:
        raise RuntimeError("Docker engine/image unavailable; check Docker Desktop and pipeline/REPRODUCE.md. No run created.") from error


def require_success(directory, config, semantic):
    for condition in config["conditions"]:
        result = json.loads((directory / condition / "evaluation/verification.json").read_text())
        if not result["formal_gate_passed"]:
            raise RuntimeError(f"Formal gate failed: {condition}")
        if semantic:
            require_pass(directory / condition / "review")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", nargs="?", default="check", choices=("check", "replay", "run"))
    parser.add_argument("--config", required=True, type=Path)
    parser.add_argument("--name", help="New sibling experiment name, required for replay/run")
    parser.add_argument("--lean", type=Path, default=Path.home() / ".elan/toolchains/leanprover--lean4---v4.28.0")
    parser.add_argument("--packages", type=Path, default=ROOT / ".lake/packages")
    parser.add_argument("--auth", type=Path,
                        default=Path(os.environ.get("RESEARCH_CODEX_AUTH", "/mnt/c/Users/austi/.codex/auth.json")))
    args = parser.parse_args(argv)
    source, config = load_config(args.config)
    check_experiment(source, config)
    if args.action == "check":
        comparison = json.loads((source / "comparison.json").read_text())
        print("Frozen records: PASS; historical code checked in Git when relocated.")
        for condition, item in comparison["conditions"].items():
            actor, verifier, critic = (item.get(key) for key in ("actor", "verification", "critic"))
            elapsed = actor.get("wall_time_seconds", "unknown") if isinstance(actor, dict) else "unknown"
            formal = verifier.get("formal_gate_passed", "unknown") if isinstance(verifier, dict) else "unknown"
            verdict = critic.get("overall_verdict", "unknown") if isinstance(critic, dict) else "unknown"
            print(f"{condition}: formal={formal}, critic={verdict}, builder_seconds={elapsed}")
        print("Evidence:", source)
        return
    if not args.name:
        parser.error("replay/run require --name; historical results are never overwritten")
    validate_name(args.name)
    target = contained(ROOT / "experiments", args.name)
    if target.exists():
        raise RuntimeError("Experiment already exists; choose a new name.")
    lean, packages, auth = (p.resolve() for p in (args.lean, args.packages, args.auth))
    prerequisites(config, lean, packages, auth, online=args.action == "run")
    current = initialize(target, source, config, replay=args.action == "replay")
    engine = Engine(target, current, lean, packages, auth, lambda: checked_record(target))
    image_id = subprocess.run(["docker", "image", "inspect", "--format", "{{.Id}}", current["image"]],
                              check=True, capture_output=True, text=True).stdout.strip()
    save(target / "runtime.json", {"image_id": image_id, "lean_path": str(lean), "packages_path": str(packages)})
    if args.action == "replay":
        engine.evaluate()
        engine.summarize()
        require_success(target, current, semantic=False)
        print("Offline replay: PASS. Critics were not rerun.")
        return
    try:
        engine.preflight()
        engine.connectivity()
        if "max_passes" in current:
            from passes import run_pair
            result = run_pair(engine)
            for condition, item in result["conditions"].items():
                print(f"{condition}: {item['outcome']}, {item['metrics']['passes_used']} passes")
            if any(item["outcome"] == "infrastructure_error" for item in result["conditions"].values()):
                raise RuntimeError("Infrastructure failure recorded; do not interpret it as a memory effect")
            return
        engine.builders()
        engine.evaluate()
        review(engine)
        engine.summarize()
        require_success(target, current, semantic=True)
    finally:
        engine.cleanup()
    print("Fresh pair passed formal gates and critics; human review remains necessary.")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, subprocess.SubprocessError, KeyError, ValueError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
