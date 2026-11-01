"""Real subprocess tests for queueing, limits, isolation, failures, and resume."""
import asyncio
from contextlib import contextmanager
import json
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

PIPELINE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PIPELINE))
import batch
import run as runner
from resources import atomic_json
from stages import execute


FAKE_WORKER = r'''
import json, pathlib, sys, time
root, delay, kind = pathlib.Path(sys.argv[1]), float(sys.argv[2]), sys.argv[3]
with (root.parent.parent / "trace.jsonl").open("a") as out:
    out.write(json.dumps({"job": root.name, "event": "start", "time": time.monotonic()}) + "\n")
time.sleep(delay)
if kind != "missing":
    value = json.loads((root / "fixture-result.json").read_text())
    if kind == "invalid": value["success"] = "yes"
    (root / "result.json").write_text(json.dumps(value))
with (root.parent.parent / "trace.jsonl").open("a") as out:
    out.write(json.dumps({"job": root.name, "event": "end", "time": time.monotonic()}) + "\n")
'''


def successful_result(job):
    record = {"schema_version": 1, "artifact_id": job["job_id"], "experiment_id": "test",
        "condition": job["condition"], "status": "verified", "success": True,
        "outcome": "accepted", "task_id": "test", "model": "test", "reasoning_effort": "medium",
        "starting_commit": "test", "artifact_snapshot": {}, "retrieved_artifacts": [],
        "verification_command": "test", "passes": [{"status": "accepted",
            "verification": {"formal_gate_passed": True}, "report": {"overall_verdict": "pass"}}],
        "metrics": {"passes_used": 1, "cost": "unknown"}, "reuse": {"approved": False}}
    return {"schema_version": 1, "job_id": job["job_id"], "pair_id": job["pair_id"],
            "condition": job["condition"], "success": True, "outcome": "accepted", "record": record}


class BatchTests(unittest.TestCase):
    def test_planner_freezes_private_identical_inputs_and_enforces_ram(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            tools = root / "pipeline"
            (tools / "docker").mkdir(parents=True)
            (tools / "worker.py").write_text("# frozen implementation\n")
            source = root / "experiments/template"
            for name in ("inputs", "memory", "evaluator"):
                (source / name).mkdir(parents=True)
            for name in ("source.txt", "source.pdf", "PROMPT.txt"):
                (source / "inputs" / name).write_text("assignment without answer")
            (source / "memory/index.md").write_text("generic memory")
            for name in runner.CONFIG_FILES:
                (source / "evaluator" / name).write_text("protected config")
            (source / "frozen-manifest.json").write_text('{"hashes": {}}')
            config = {"name": "template", "task_id": "test", "model": "test",
                      "reasoning_effort": "medium", "conditions": ["stateless", "retrieved"],
                      "max_passes": 1, "builder_seconds": 1, "critic_seconds": 1,
                      "image": "test", "inputs": "inputs", "memory": "memory", "evaluator": "evaluator",
                      "resources": {"memory": "1g", "cpus": 1, "pids": 32}}
            atomic_json(source / "experiment.json", config)
            spec = {"schema_version": 1, "limits": {"jobs": 2, "model_calls": 1,
                    "lean_builds": 2, "ram_gib": 8, "job_seconds": 60},
                    "tasks": [{"id": "test", "config": "experiments/template/experiment.json",
                    "trials": 1, "memory_review": {"target_answer_excluded": True, "note": "generic notes only"}}]}
            atomic_json(root / "spec.json", spec)
            target = root / "experiments/batch"
            with patch.object(batch, "ROOT", root), patch.object(runner, "ROOT", root), \
                 patch.object(batch, "PIPELINE", tools), patch.object(runner, "PIPELINE", tools), \
                 patch("run.subprocess.run", return_value=SimpleNamespace(stdout="test-commit")):
                plan = batch.prepare(root / "spec.json", target)
                batch.check_plan(target)
                for job in plan["jobs"]:
                    private = target / job["directory"]
                    self.assertEqual((private / "memory/index.md").read_text(), "generic memory")
                    self.assertEqual((private / "stateless/workspace/Research/Submission.lean").read_text(), "import Mathlib\n")
                    self.assertTrue((private / "runtime-source/pipeline/worker.py").exists())
                    # A completed worker updates this generated index. That is
                    # output, not immutable mathematical input for the next job.
                    (private / "artifacts/index.md").write_text("new run summary")
                    batch.check_plan(target)
                (source / "memory/index.md").write_text("later source change")
                batch.check_plan(target)
                spec["limits"]["ram_gib"] = 1
                atomic_json(root / "spec.json", spec)
                with self.assertRaisesRegex(ValueError, "RAM budget"):
                    batch.prepare(root / "spec.json", root / "experiments/rejected")
                self.assertFalse((root / "experiments/rejected").exists())

    def fixture(self, root, pairs=3):
        jobs = []
        (root / "artifacts").mkdir()
        for index in range(pairs):
            for condition in ("stateless", "retrieved"):
                pair = f"task-{index}"
                identity = pair + "-" + condition
                job = {"job_id": identity, "pair_id": pair, "task_id": "test",
                       "condition": condition, "directory": "runs/" + identity}
                path = root / job["directory"]
                path.mkdir(parents=True)
                atomic_json(path / "fixture-result.json", successful_result(job))
                jobs.append(job)
        plan = {"jobs": jobs, "limits": {"jobs": 2, "job_seconds": 10}}
        atomic_json(root / "plan.json", plan)
        atomic_json(root / "batch-manifest.json", {"hashes": {"plan.json": batch.digest(root / "plan.json")}})
        queue = batch.Queue(root)
        for job in jobs:
            queue.add(job)
        queue.close()
        return plan

    def command(self, root, job, delay="0.05", kind="valid"):
        return [sys.executable, "-c", FAKE_WORKER, str(root / job["directory"]), delay, kind]

    def test_phase_barrier_bounded_concurrency_and_refill(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            self.fixture(root)
            def command(job):
                delay = "0.6" if job["job_id"] == "task-0-stateless" else "0.08"
                return self.command(root, job, delay)
            rows = asyncio.run(batch.coordinate(root, command, cleanup=lambda root: None))
            self.assertTrue(all(row["state"] == "finished" for row in rows))
            events = [json.loads(line) for line in (root / "trace.jsonl").read_text().splitlines()]
            live = maximum = 0
            times = {}
            for event in sorted(events, key=lambda item: item["time"]):
                live += 1 if event["event"] == "start" else -1
                maximum = max(maximum, live)
                times[event["job"], event["event"]] = event["time"]
            self.assertEqual(maximum, 2)
            self.assertLess(times["task-2-stateless", "start"], times["task-0-stateless", "end"])
            self.assertLess(max(value for (job, event), value in times.items() if job.endswith("stateless") and event == "end"),
                            min(value for (job, event), value in times.items() if job.endswith("retrieved") and event == "start"))
            self.assertEqual(len(batch.read(root / "comparison.json")["pairs"]), 3)

    def test_collection_preserves_curated_artifact_index(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            plan = self.fixture(root, pairs=1)
            (root / "artifacts/index.md").write_text("curated research summary")
            queue = batch.Queue(root)
            batch.collect(root, queue, plan)
            queue.close()
            self.assertEqual((root / "artifacts/index.md").read_text(), "curated research summary")
            self.assertTrue((root / "artifacts/jobs.md").exists())

    def test_invalid_and_missing_reports_are_infrastructure_errors(self):
        for kind in ("missing", "invalid"):
            with self.subTest(kind=kind), TemporaryDirectory() as folder:
                root = Path(folder)
                self.fixture(root, pairs=1)
                rows = asyncio.run(batch.coordinate(root, lambda job: self.command(root, job, kind=kind), cleanup=lambda root: None))
                self.assertTrue(all(json.loads(row["result"])["outcome"] == "infrastructure_error" for row in rows))

    def test_timeout_preserves_evidence_and_finishes_queue(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            plan = self.fixture(root, pairs=1)
            plan["limits"]["job_seconds"] = 0.15
            atomic_json(root / "plan.json", plan)
            atomic_json(root / "batch-manifest.json", {"hashes": {"plan.json": batch.digest(root / "plan.json")}})
            cleaned = []
            rows = asyncio.run(batch.coordinate(root, lambda job: self.command(root, job, delay="5"), cleanup=lambda path: cleaned.append(path)))
            self.assertEqual(len(cleaned), 2)
            self.assertTrue(all("timeout" in json.loads(row["result"])["error"] for row in rows))
            self.assertTrue((root / "trace.jsonl").exists())

    def test_interrupted_job_is_preserved_and_finished_jobs_not_replayed(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            plan = self.fixture(root, pairs=1)
            queue = batch.Queue(root)
            queue.claim(plan["jobs"][0]["job_id"])
            queue.close()
            calls = []
            def command(job):
                calls.append(job["job_id"])
                return self.command(root, job)
            first = asyncio.run(batch.coordinate(root, command, cleanup=lambda path: None))
            self.assertEqual(calls, [plan["jobs"][1]["job_id"]])
            self.assertEqual(json.loads(first[0]["result"])["outcome"], "infrastructure_error")
            second = asyncio.run(batch.coordinate(root, command, cleanup=lambda path: None))
            self.assertEqual(len(calls), 1)
            self.assertEqual(first, second)

    def test_frozen_input_tampering_fails_before_launch(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            self.fixture(root, pairs=1)
            (root / "plan.json").write_text("{}")
            command = Mock()
            with self.assertRaisesRegex(RuntimeError, "Frozen batch input changed"):
                asyncio.run(batch.coordinate(root, command, cleanup=lambda root: None))
            command.assert_not_called()

    def test_duplicate_coordinator_is_rejected(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            self.fixture(root, pairs=1)
            with batch.coordinator_lock(root):
                with self.assertRaisesRegex(RuntimeError, "already owns"):
                    asyncio.run(batch.coordinate(root, Mock(), cleanup=lambda root: None))

    def test_success_requires_both_actual_gates(self):
        job = {"job_id": "test", "pair_id": "pair", "task_id": "test", "condition": "stateless"}
        value = successful_result(job)
        value["record"]["passes"][-1]["verification"]["formal_gate_passed"] = False
        with self.assertRaisesRegex(ValueError, "formal and semantic"):
            batch.validate_result(value, job)

    def test_collected_artifacts_are_searchable_with_job_identity(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            plan = self.fixture(root, pairs=1)
            queue = batch.Queue(root)
            job = plan["jobs"][0]
            value = successful_result(job)
            value["record"]["candidate_lessons"] = [{"requirement": "componentwise perturbation"}]
            queue.finish(job["job_id"], value)
            hits = queue.search("perturbation")
            self.assertEqual(len(hits), 1)
            self.assertEqual(hits[0][0], job["job_id"])
            self.assertIn("perturbation", hits[0][1])
            queue.close()

    def test_pass_gates_run_in_order_and_skip_critic_on_failed_verification(self):
        engine = SimpleNamespace()
        calls = []
        @contextmanager
        def gate(stage):
            calls.append(stage)
            yield
        with patch("stages.build", return_value={"exit_code": 0}), patch("stages.verify", return_value={"formal_gate_passed": False}), patch("stages.critique") as critic:
            result = execute(engine, "stateless", gate=gate)
        self.assertEqual(calls, ["builder", "verification"])
        self.assertEqual(result["status"], "formal_failed")
        critic.assert_not_called()


if __name__ == "__main__":
    unittest.main()
