"""One WSL entry point for the frozen pilot, offline replay, and fresh pairs.

The historical controller is deliberately unchanged: its hashes are evidence.
This adapter supplies portable paths and new output locations, not proof hints.
"""
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

ROOT = Path(__file__).resolve().parents[1]
ENGINE = ROOT / "pipeline/isolated_experiment"
DEFAULT = ROOT / "experiments/memory-ablation/2026-10-19-binary-tree-pilot-gpt61"
# Preserve the exact README hashed by the pilot while updating the live guide.
HISTORICAL_README = "pipeline/isolated_experiment/README.md"
HISTORICAL_DOC_COMMIT = "e92d0cef1cdd8f209800df878637c0905284032b"
sys.path.insert(0, str(ENGINE))
import retry_pair as pilot


def checked_template(path):
    path = path.resolve()
    manifest = json.loads((path / "frozen-manifest.json").read_text())
    for name, expected in manifest["hashes"].items():
        file = (ROOT / name).resolve()
        if not file.is_relative_to(ROOT) or file.is_symlink():
            raise RuntimeError(f"Unsafe frozen path: {name}")
        if hashlib.sha256(file.read_bytes()).hexdigest() != expected:
            if name == HISTORICAL_README:
                original = subprocess.run(
                    ["git", "-C", str(ROOT), "show", f"{HISTORICAL_DOC_COMMIT}:{name}"],
                    check=True, capture_output=True, timeout=10).stdout
                if hashlib.sha256(original).hexdigest() == expected:
                    print("README updated; original documentation hash verified in Git.")
                    continue
            raise RuntimeError(f"Frozen input changed: {name}")
    return manifest


def configure(args, manifest):
    engine = pilot.run
    engine.MODEL = manifest["model"]
    engine.EFFORT = manifest["reasoning_effort"]
    engine.LEAN = args.lean.resolve()
    engine.PACKAGES = args.packages.resolve()
    engine.AUTH = args.auth.resolve()
    # Strict input checks, with only the documented historical-README case.
    engine.check_frozen = lambda: checked_template(engine.RUN)
    if args.run_id:
        if not re.fullmatch(r"[a-z0-9][a-z0-9-]{0,63}", args.run_id):
            raise RuntimeError("run-id must be 1–64 lowercase letters, numbers or hyphens")
        engine.RUN = ROOT / "experiments/memory-ablation" / args.run_id
        engine.NET = f"research-{args.run_id}-internal"
        engine.PROXY = f"research-{args.run_id}-proxy"
    return engine


def prerequisites(engine, online):
    if sys.platform != "linux":
        raise RuntimeError("Run this command inside WSL/Linux, not PowerShell.")
    for path in (engine.LEAN / "bin/lean", engine.PACKAGES / "mathlib"):
        if not path.exists():
            raise RuntimeError(f"Missing dependency: {path}. See pipeline/REPRODUCE.md")
    if online and not engine.AUTH.is_file():
        raise RuntimeError("Authentication file missing; supply --auth. Never place it in the repository.")
    try:
        subprocess.run(["docker", "info"], check=True, stdout=subprocess.DEVNULL,
                       stderr=subprocess.PIPE, timeout=20)
    except subprocess.SubprocessError as error:
        raise RuntimeError("Docker engine is unavailable. Start/check Docker Desktop and its WSL integration; no run was created.") from error
    subprocess.run(["docker", "image", "inspect", engine.IMAGE], check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, timeout=20)


def initialize(engine, template, old_manifest, replay):
    # Exclusive creation prevents overwriting any completed or partial attempt.
    engine.RUN.mkdir(parents=True, exist_ok=False)
    for folder in ("spec", "memory", "trusted"):
        shutil.copytree(template / folder, engine.RUN / folder)
    for condition in engine.CONDITIONS:
        work = engine.RUN / condition / "workspace"
        (work / "Research").mkdir(parents=True)
        (work / ".lake").mkdir()
        for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "Research.lean"):
            shutil.copyfile(engine.RUN / "trusted" / name, work / name)
        if replay:
            source = template / condition / "workspace/Research"
            for file in source.rglob("*.lean"):
                if file.is_symlink():
                    raise RuntimeError("Submission symlink rejected")
                dest = work / "Research" / file.relative_to(source)
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(file, dest)
        else:
            (work / "Research/Submission.lean").write_text("import Mathlib\n")
        out = engine.RUN / condition / "output"
        out.mkdir()
        engine.ownership(work)
        engine.ownership(out)
    tracked = [p for folder in ("spec", "memory", "trusted")
               for p in (engine.RUN / folder).rglob("*") if p.is_file()]
    tracked += [p for p in ENGINE.iterdir() if p.is_file()]
    tracked += [Path(__file__).resolve()]
    if replay:
        tracked += list(engine.RUN.glob("*/workspace/Research/**/*.lean"))
    manifest = dict(old_manifest)
    manifest.update(experiment_id=engine.RUN.name,
                    starting_commit=engine.call(["git", "-C", ROOT, "rev-parse", "HEAD"]).stdout.strip(),
                    template=str(template.relative_to(ROOT)),
                    template_manifest_sha256=engine.digest(template / "frozen-manifest.json"),
                    mode="offline-replay" if replay else "fresh-pair",
                    frozen_unix=time.time(),
                    hashes={str(p.relative_to(ROOT)): engine.digest(p) for p in tracked})
    manifest.pop("pre_actor_infrastructure_revisions", None)
    engine.save(engine.RUN / "frozen-manifest.json", manifest)
    engine.save(engine.RUN / "README.md", "# " + engine.RUN.name + "\n\n"
                + ("Offline replay of saved sources. No builders or critics rerun.\n" if replay else
                   "Fresh pair from frozen inputs. No source from prior submissions supplied.\n"))


def formal_results(engine):
    results = {}
    for condition in engine.CONDITIONS:
        results[condition] = json.loads((engine.RUN / condition / "evaluation/verification.json").read_text())
    if not all(result["formal_gate_passed"] for result in results.values()):
        raise RuntimeError("At least one formal gate failed; inspect the evaluation logs.")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("check", "replay", "run"))
    parser.add_argument("--run-id", help="New output directory; required for replay/run")
    parser.add_argument("--template", type=Path, default=DEFAULT)
    parser.add_argument("--lean", type=Path, default=Path.home() / ".elan/toolchains/leanprover--lean4---v4.28.0")
    parser.add_argument("--packages", type=Path, default=ROOT / ".lake/packages")
    parser.add_argument("--auth", type=Path, default=Path(os.environ.get("RESEARCH_CODEX_AUTH", "/mnt/c/Users/austi/.codex/auth.json")))
    args = parser.parse_args(argv)
    if args.action != "check" and not args.run_id:
        parser.error("replay/run require --run-id; previous results are never overwritten")
    template = args.template.resolve()
    if not template.is_relative_to(ROOT):
        parser.error("template must be inside the repository")
    manifest = checked_template(template)
    if args.action == "check":
        print("Frozen input hashes: PASS")
        comparison = json.loads((template / "comparison.json").read_text())
        print("Experiment:", comparison["experiment_id"])
        for condition, item in comparison["conditions"].items():
            actor = item.get("actor")
            verification = item.get("verification")
            critic = item.get("critic")
            elapsed = actor.get("wall_time_seconds", "unknown") if isinstance(actor, dict) else "unknown"
            formal = verification.get("formal_gate_passed", "unknown") if isinstance(verification, dict) else "unknown"
            semantic = critic.get("overall_verdict", "unknown") if isinstance(critic, dict) else "unknown"
            print(f"{condition}: formal={formal}, critic={semantic}, builder_seconds={elapsed}")
        print("Full evidence:", template)
        return
    engine = configure(args, manifest)
    prerequisites(engine, online=args.action == "run")
    initialize(engine, template, manifest, replay=args.action == "replay")
    image_id = engine.call(["docker", "image", "inspect", "--format", "{{.Id}}", engine.IMAGE]).stdout.strip()
    engine.save(engine.RUN / "runtime.json", {"image_id": image_id, "lean_path": str(engine.LEAN),
                                            "packages_path": str(engine.PACKAGES)})
    if args.action == "replay":
        engine.evaluate()
        engine.summarize()
        formal_results(engine)
        print("Offline replay: PASS. Semantic critics were not rerun.")
        return
    try:
        engine.preflight()
        if pilot.connectivity() != 0:
            raise RuntimeError("Connectivity test failed; no proof builders launched")
        engine.builders()
        engine.evaluate()
        engine.review()
        engine.summarize()
        formal_results(engine)
        for condition in engine.CONDITIONS:
            verdict = json.loads((engine.RUN / condition / "review/review.json").read_text())
            if verdict.get("overall_verdict") != "pass":
                raise RuntimeError(f"Semantic review did not pass: {condition}")
    finally:
        engine.cleanup()
    print("Fresh pair: formal gates and semantic critics PASS. Human review still required.")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, subprocess.SubprocessError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
