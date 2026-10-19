"""Critic orchestration on the host and reviewer entry point in the container.

The experiment supplies the rubric. Shared session logging lives in agent.py;
shared Docker isolation lives in engine.py. Neither the builder's conversation
nor its memory snapshot is supplied to the critic.
"""
import json
from pathlib import Path
import shutil
import subprocess

from agent import run_agent


def reviewer_prompt(spec=Path("/spec")):
    return (spec / "REVIEWER.txt").read_text()


def review(engine):
    """Launch one fresh, read-only-candidate critic per experimental condition."""
    # Host-only helpers are not needed or mounted inside the reviewer container.
    from engine import TOOLS, mount, ownership, save

    engine.guard()
    engine.network()
    for condition in engine.conditions:
        spec = engine.directory / condition / "reviewer-spec"
        spec.mkdir()
        for name in ("source.txt", "source.pdf"):
            shutil.copyfile(engine.directory / engine.config["inputs"] / name, spec / name)
        shutil.copyfile(engine.directory / engine.config["evaluator"] / "REVIEWER.txt", spec / "REVIEWER.txt")
        output = engine.directory / condition / "review"
        output.mkdir()
        ownership(output)
        with (output / "container.log").open("w") as log:
            result = subprocess.run([*engine.container(condition,
                workspace=engine.directory / condition / "evaluation-workspace", output=output,
                spec=spec, reviewer=True),
                *mount(engine.directory / condition / "evaluation", "/evaluation", True),
                *mount(TOOLS / "critic.py", "/runner/critic.py", True),
                engine.image, "python3", "/runner/critic.py"], stdout=log, stderr=subprocess.STDOUT,
                timeout=engine.config["critic_seconds"] + 60)
        save(output / "container-exit.json", {"exit_code": result.returncode})


def require_pass(directory):
    """Fail closed on missing/invalid reports or a non-pass critic verdict."""
    report = json.loads((directory / "review.json").read_text())
    if not isinstance(report, dict) or report.get("overall_verdict") != "pass":
        raise RuntimeError(f"Critic did not pass: {directory.parent.name}")


def main():
    run_agent(reviewer_prompt(), kind="reviewer")


if __name__ == "__main__":
    main()
