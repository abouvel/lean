"""Prepare frozen calibration cases; expected labels are host-only."""
import hashlib
import json
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT / "experiments/exp-011-dot-product-critic-2026-10-28"
CASES = {"known-complete": "pass", "renamed-complete": "pass",
         "proposition-only": "fail", "additions-only": "fail",
         "zero-u-only": "fail", "conclusion-assumed": "fail"}


def main():
    for folder in ("inputs", "evaluator", "memory"):
        shutil.copytree(SOURCE / folder, HERE / folder)
    for case in CASES:
        shutil.copytree(SOURCE / case / "evaluation-workspace", HERE / case / "workspace",
                        ignore=shutil.ignore_patterns(".lake"))
        (HERE / case / "workspace/.lake/packages").mkdir(parents=True)
    config = json.loads((SOURCE / "experiment.json").read_text())
    config.update(name=HERE.name, conditions=list(CASES), critic_seconds=180,
        revision={"schema_version":1, "mode":"calibration",
                  "seconds":{role:180 for role in ("planner","formalizer","prover","translator","judge")}})
    (HERE / "experiment.json").write_text(json.dumps(config,indent=2)+"\n")
    protocol = {"experiment_id": HERE.name, "kind":"semantic-evaluator-calibration",
        "model":config["model"], "reasoning_effort":config["reasoning_effort"],
        "seconds_per_evaluator":180, "expected_verdicts":CASES,
        "acceptance_tests":["All candidate formal gates pass before model calls",
            "All six blind translations and round-trip reports validate",
            "Round-trip verdicts match all hidden case labels with no false pass or false rejection",
            "Direct/round-trip agreements are measured, and disagreements are retained for human adjudication"],
        "human_review":"pending; controlled mutation labels do not substitute for expert validation on natural tasks"}
    (HERE / "protocol.json").write_text(json.dumps(protocol,indent=2)+"\n")


if __name__ == "__main__": main()
