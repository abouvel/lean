"""Run exactly one theorem/trial/condition in a private subprocess."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import sys

import run as runner

from engine import Engine
from passes import run_condition
from resources import Heartbeat, ResourcePool, atomic_json
from run import checked_record, prerequisites


def decorate(engine, label, network):
    original = engine.container

    def container(*args, **kwargs):
        command = original(*args, **kwargs)
        return command[:3] + ["--label", "research.job=" + label] + command[3:]

    engine.container = container
    engine.net, engine.proxy = network + "-internal", network + "-proxy"
    engine.decorate_child = lambda child: decorate(child, label, network)


def run_job(batch, job, lean, packages, auth):
    plan = json.loads((batch / "plan.json").read_text())
    # This worker executes from the archived implementation, while frozen input
    # paths in the legacy manifests remain relative to the original repository.
    runner.ROOT = Path(plan["repository_root"])
    from batch import check_plan
    check_plan(batch)
    root = batch / job["directory"]
    config = json.loads((root / "experiment.json").read_text())
    mode = job["condition"]
    pool = ResourcePool(batch / "leases", json.loads((batch / "plan.json").read_text())["limits"])
    prerequisites(config, lean, packages, auth, online=True)
    def guard():
        check_plan(batch)
        checked_record(root)
    engine = Engine(root, config, lean, packages, auth, guard)
    engine.conditions = (mode,)
    identity = hashlib.sha256(str(root).encode()).hexdigest()[:24]
    decorate(engine, identity, "research-" + identity)
    with Heartbeat(root / "heartbeat.json", job["job_id"]) as heartbeat:
        engine.stage_gate = lambda stage: heartbeat.stage(pool, stage)
        try:
            with engine.stage_gate("preflight"):
                engine.preflight()
            with engine.stage_gate("connectivity"):
                engine.connectivity()
            record = run_condition(engine, mode)
            atomic_json(root / "result.json", {"schema_version": 1,
                "job_id": job["job_id"], "pair_id": job["pair_id"],
                "condition": mode, "success": record["success"],
                "outcome": record["outcome"], "record": record})
        finally:
            engine.cleanup()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batch", required=True, type=Path)
    parser.add_argument("--job", required=True)
    parser.add_argument("--lean", required=True, type=Path)
    parser.add_argument("--packages", required=True, type=Path)
    parser.add_argument("--auth", required=True, type=Path)
    args = parser.parse_args()
    batch = args.batch.resolve()
    plan = json.loads((batch / "plan.json").read_text())
    job = next(item for item in plan["jobs"] if item["job_id"] == args.job)

    def interrupted(signum, frame):
        raise InterruptedError(f"Worker interrupted by signal {signum}")

    signal.signal(signal.SIGTERM, interrupted)
    try:
        run_job(batch, job, args.lean.resolve(), args.packages.resolve(), args.auth.resolve())
    except Exception as error:
        root = batch / job["directory"]
        atomic_json(root / "result.json", {"schema_version": 1,
            "job_id": job["job_id"], "pair_id": job["pair_id"],
            "condition": job["condition"], "success": False,
            "outcome": "infrastructure_error", "error": str(error)})
        print(str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
