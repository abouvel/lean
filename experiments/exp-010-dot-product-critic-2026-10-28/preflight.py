"""Run all formal gates before freezing or making any model request."""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
from run_benchmark import verify_cases
sys.path.insert(0, str(ROOT / "pipeline"))
from engine import Engine

config = json.loads((HERE / "experiment.json").read_text())
engine = Engine(HERE, config,
                Path.home() / ".elan/toolchains/leanprover--lean4---v4.28.0",
                ROOT / ".lake/packages", Path("/nonexistent-auth"), lambda: None)
verify_cases(config, engine)
print("ALL_FORMAL_GATES_PASS")
