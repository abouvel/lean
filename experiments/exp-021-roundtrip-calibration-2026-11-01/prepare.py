"""Fresh calibration ID using unchanged verified cases after export-permission repair."""
import json
from pathlib import Path
import shutil

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/"experiments/exp-018-roundtrip-calibration-2026-11-01"

if __name__ == "__main__":
    for folder in ("inputs","evaluator","memory"):
        shutil.copytree(SOURCE/folder,HERE/folder)
    config=json.loads((SOURCE/"experiment.json").read_text())
    config["name"]=HERE.name
    (HERE/"experiment.json").write_text(json.dumps(config,indent=2)+"\n")
    protocol=json.loads((SOURCE/"protocol.json").read_text())
    protocol.update(experiment_id=HERE.name,preflight_source=SOURCE.name,
        reason="Fresh run after owner-only atomic-report export failure; no mathematical inputs or budgets changed")
    (HERE/"protocol.json").write_text(json.dumps(protocol,indent=2)+"\n")
    for case in config["conditions"]:
        for folder in ("workspace","evaluation-workspace","evaluation","formal-audit/dependencies"):
            shutil.copytree(SOURCE/case/folder,HERE/case/folder)
    shutil.copyfile(SOURCE/"run_calibration.py",HERE/"run_calibration.py")
