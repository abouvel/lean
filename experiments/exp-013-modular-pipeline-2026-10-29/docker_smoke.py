"""Exercise the archived worker's frozen guard and real Docker preflight only."""
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]
sys.path.insert(0, str(HERE / "runtime-source/pipeline"))
import run as runner
from batch import check_plan
from engine import Engine
from worker import decorate

runner.ROOT = REPOSITORY
plan = json.loads((HERE / "plan.json").read_text())
job = plan["jobs"][0]
root = HERE / job["directory"]
config = json.loads((root / "experiment.json").read_text())

def guard():
    check_plan(HERE)
    runner.checked_record(root)

guard()
engine = Engine(root, config,
                Path.home() / ".elan/toolchains/leanprover--lean4---v4.28.0",
                REPOSITORY / ".lake/packages",
                Path("/mnt/c/Users/austi/.codex/auth.json"), guard)
engine.conditions = (job["condition"],)
identity = hashlib.sha256(str(root).encode()).hexdigest()[:24]
decorate(engine, identity, "research-" + identity)
try:
    engine.preflight()
finally:
    engine.cleanup()
guard()
print("ARCHIVED_RUNTIME_AND_DOCKER_PREFLIGHT_PASS; no model calls")
