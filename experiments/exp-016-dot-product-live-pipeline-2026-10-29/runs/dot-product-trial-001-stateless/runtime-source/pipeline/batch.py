"""Plan, run, resume, and inspect a bounded queue of isolated proof jobs (Linux)."""
import argparse
import asyncio
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import sqlite3
import subprocess
import sys
import time

from artifacts import validate as validate_artifact
from resources import atomic_json
from run import ROOT, PIPELINE, contained, digest, initialize, load_config, validate_name

# Archived coordinators retain repository-relative input paths while executing
# the implementation bytes frozen inside the batch.
if PIPELINE.parent.name == "runtime-source":
    archived_plan = PIPELINE.parents[1] / "plan.json"
    if archived_plan.is_file():
        import run as runner
        ROOT = Path(json.loads(archived_plan.read_text())["repository_root"])
        runner.ROOT = ROOT

OUTCOMES = {"accepted", "formal_failed", "critic_failed", "needs_human", "infrastructure_error"}


def read(path):
    return json.loads(Path(path).read_text())


def check_plan(directory):
    manifest = read(directory / "batch-manifest.json")
    for name, expected in manifest["hashes"].items():
        if digest(contained(directory, name)) != expected:
            raise RuntimeError(f"Frozen batch input changed: {name}")


def validate_spec(spec):
    if spec.get("schema_version") != 1 or not spec.get("tasks"):
        raise ValueError("Batch needs schema_version 1 and a nonempty tasks list")
    limits = spec["limits"]
    for key in ("jobs", "model_calls", "lean_builds", "ram_gib", "job_seconds"):
        if type(limits.get(key)) is not int or limits[key] <= 0:
            raise ValueError(f"limits.{key} must be a positive integer")
    if limits["model_calls"] > limits["jobs"] or limits["lean_builds"] > limits["jobs"]:
        raise ValueError("Resource slots cannot exceed the job slot count")
    ids = []
    for task in spec["tasks"]:
        validate_name(task["id"])
        if len(task["id"]) > 40:
            raise ValueError("Task IDs must be at most 40 characters")
        ids.append(task["id"])
        if type(task.get("trials")) is not int or task["trials"] <= 0:
            raise ValueError("trials must be a positive integer")
        review = task.get("memory_review", {})
        if review.get("target_answer_excluded") is not True or not str(review.get("note", "")).strip():
            raise ValueError("Each task needs a documented memory review excluding its target answer")
    if len(ids) != len(set(ids)):
        raise ValueError("Duplicate task ID")


def prepare(spec_path, target):
    """Planning is offline: snapshot inputs, assign conditions, initialize queue."""
    spec = read(spec_path)
    validate_spec(spec)
    if target.exists():
        raise FileExistsError("Batch exists; use run/status, or choose a new experiment name")
    # Validate every source and budget before creating anything.
    tasks = []
    for task in spec["tasks"]:
        source, config = load_config(contained(ROOT, task["config"]))
        if not (source / "frozen-manifest.json").is_file():
            raise ValueError("Task template must have a source manifest")
        config = dict(config)
        config["max_passes"] = config.get("max_passes", 1)
        for key in ("max_passes", "builder_seconds", "critic_seconds"):
            if type(config.get(key)) is not int or config[key] <= 0:
                raise ValueError(f"Task {key} must be a positive integer")
        if config.get("critic_memory_enabled"):
            raise ValueError("Proof-memory ablations keep critics independent of builder memory")
        memory = config["resources"]["memory"]
        if not isinstance(memory, str) or not memory.endswith("g"):
            raise ValueError("Batch resources.memory must be a whole GiB value such as 8g")
        memory_gib = int(memory[:-1])
        if memory_gib <= 0 or spec["limits"]["jobs"] * (memory_gib + 3) > spec["limits"]["ram_gib"]:
            raise ValueError("RAM budget must cover jobs * (container GiB + 3 GiB tmpfs/proxy overhead)")
        for key in ("source.txt", "source.pdf", "PROMPT.txt"):
            if not (source / config["inputs"] / key).is_file():
                raise ValueError(f"Missing builder task input: {key}")
        tasks.append((task, source, config))

    target.mkdir(parents=True)
    runtime = target / "runtime-source/pipeline"
    runtime.mkdir(parents=True)
    for file in PIPELINE.iterdir():
        if file.suffix in (".py", ".sh"):
            shutil.copyfile(file, runtime / file.name)
    shutil.copytree(PIPELINE / "docker", runtime / "docker")
    jobs = []
    for task, source, config in tasks:
        for trial in range(1, task["trials"] + 1):
            pair_id = f"{task['id']}-trial-{trial:03d}"
            for condition in ("stateless", "retrieved"):
                job_id = pair_id + "-" + condition
                # Docker network names must also remain short and unique.
                if len(job_id) > 100:
                    raise ValueError("Combined task/trial job ID is too long")
                directory = target / "runs" / job_id
                directory.parent.mkdir(exist_ok=True)
                initialize(directory, source, config, replay=False)
                # Preserve implementation bytes for the legacy manifest checker.
                shutil.copytree(target / "runtime-source", directory / "runtime-source")
                jobs.append({"job_id": job_id, "pair_id": pair_id,
                    "task_id": config["task_id"], "trial": trial,
                    "condition": condition, "directory": str(directory.relative_to(target))})
    plan = {"schema_version": 1, "experiment_id": target.name,
        "repository_root": str(ROOT), "order": "stateless-phase-first",
        "limits": spec["limits"], "tasks": spec["tasks"], "jobs": jobs,
        "created_unix": time.time()}
    atomic_json(target / "plan.json", plan)
    frozen = [target / "plan.json"]
    frozen.extend(path for path in (target / "runtime-source").rglob("*") if path.is_file())
    for job in jobs:
        directory = target / job["directory"]
        frozen.extend(path for path in directory.rglob("*") if path.is_file())
    atomic_json(target / "batch-manifest.json", {"schema_version": 1,
        "hashes": {str(path.relative_to(target)): digest(path) for path in frozen}})
    queue = Queue(target)
    for job in jobs:
        queue.add(job)
    queue.close()
    atomic_json(target / "comparison.json", {"schema_version": 1, "pairs": {}})
    (target / "artifacts").mkdir()
    (target / "artifacts/index.md").write_text("# Batch artifacts\n\n- [Collected job results](jobs.md)\n")
    (target / "artifacts/jobs.md").write_text("# Batch results\n\nNo jobs have finished.\n")
    return plan


class Queue:
    """Only the coordinator writes this SQLite queue. Workers write private files."""
    def __init__(self, directory):
        self.directory = Path(directory)
        self.db = sqlite3.connect(self.directory / "queue.sqlite3")
        self.db.execute("CREATE TABLE IF NOT EXISTS jobs (job_id TEXT PRIMARY KEY, condition TEXT NOT NULL, state TEXT NOT NULL, pid INTEGER, started REAL, finished REAL, result TEXT)")
        self.db.execute("CREATE VIRTUAL TABLE IF NOT EXISTS artifact_search USING fts5(job_id UNINDEXED, body)")
        self.db.commit()

    def add(self, job):
        self.db.execute("INSERT INTO jobs(job_id,condition,state) VALUES(?,?,'queued')", (job["job_id"], job["condition"]))
        self.db.commit()

    def rows(self):
        self.db.row_factory = sqlite3.Row
        return [dict(row) for row in self.db.execute("SELECT * FROM jobs ORDER BY rowid")]

    def claim(self, job_id):
        changed = self.db.execute("UPDATE jobs SET state='running',started=? WHERE job_id=? AND state='queued'", (time.time(), job_id)).rowcount
        self.db.commit()
        if changed != 1:
            raise RuntimeError("Job was already claimed: " + job_id)

    def pid(self, job_id, pid):
        self.db.execute("UPDATE jobs SET pid=? WHERE job_id=?", (pid, job_id))
        self.db.commit()

    def finish(self, job_id, result):
        self.db.execute("UPDATE jobs SET state='finished',finished=?,result=? WHERE job_id=?", (time.time(), json.dumps(result), job_id))
        self.db.execute("DELETE FROM artifact_search WHERE job_id=?", (job_id,))
        self.db.execute("INSERT INTO artifact_search(job_id,body) VALUES(?,?)", (job_id, json.dumps(result)))
        self.db.commit()

    def search(self, query):
        return self.db.execute("SELECT job_id, snippet(artifact_search,1,'[',']','...',32) FROM artifact_search WHERE artifact_search MATCH ? ORDER BY rank LIMIT 20", (query,)).fetchall()

    def close(self):
        self.db.close()


def validate_result(value, job):
    if not isinstance(value, dict) or value.get("schema_version") != 1:
        raise ValueError("Invalid result bundle")
    for key in ("job_id", "pair_id", "condition"):
        if value.get(key) != job[key]:
            raise ValueError("Wrong result identity: " + key)
    if type(value.get("success")) is not bool or value.get("outcome") not in OUTCOMES:
        raise ValueError("Invalid result outcome")
    if value["success"] != (value["outcome"] == "accepted"):
        raise ValueError("Contradictory success")
    if value["outcome"] != "infrastructure_error":
        validate_artifact(value["record"])
        record = value["record"]
        if (record["condition"] != job["condition"] or record["task_id"] != job["task_id"] or
                record["success"] != value["success"] or record["outcome"] != value["outcome"]):
            raise ValueError("Result and run record disagree")
        if value["success"]:
            final = record["passes"][-1]
            if final.get("verification", {}).get("formal_gate_passed") is not True or final.get("report", {}).get("overall_verdict") != "pass":
                raise ValueError("Acceptance requires formal and semantic gates")
    return value


def infrastructure(job, error):
    return {"schema_version": 1, "job_id": job["job_id"], "pair_id": job["pair_id"],
            "condition": job["condition"], "success": False,
            "outcome": "infrastructure_error", "error": str(error)}


def collect(directory, queue, plan):
    """Publish comparisons as soon as both partners finish; keep every failure."""
    results = {row["job_id"]: json.loads(row["result"]) for row in queue.rows() if row["state"] == "finished"}
    pairs = {}
    for job in plan["jobs"]:
        partner = next(item for item in plan["jobs"] if item["pair_id"] == job["pair_id"] and item["condition"] != job["condition"])
        if job["job_id"] in results and partner["job_id"] in results:
            pair = pairs.setdefault(job["pair_id"], {})
            value = results[job["job_id"]]
            pair[job["condition"]] = {key: value[key] for key in ("job_id", "success", "outcome")}
            pair[job["condition"]]["metrics"] = value.get("record", {}).get("metrics", {"cost": "unknown", "tokens": "unknown"})
    atomic_json(directory / "comparison.json", {"schema_version": 1, "pairs": pairs})
    lines = ["# Batch results", "", "| Job | Condition | Outcome | Evidence |", "| --- | --- | --- | --- |"]
    for job in reversed(plan["jobs"]):
        if job["job_id"] in results:
            value = results[job["job_id"]]
            lines.append(f"| {job['job_id']} | {job['condition']} | {value['outcome']} | [Result](../{job['directory']}/collected-result.json) |")
    # Keep curated summaries in index.md intact when later jobs finish.
    (directory / "artifacts/jobs.md").write_text("\n".join(lines) + "\n")


def cleanup_containers(root):
    """Remove only containers carrying this exact job identity; retain all files."""
    identity = hashlib.sha256(str(root).encode()).hexdigest()[:24]
    for command in (["docker", "ps", "-aq", "--filter", "label=research.job=" + identity],):
        found = subprocess.run(command, capture_output=True, text=True, timeout=20)
        if found.returncode:
            raise RuntimeError("Cannot inspect Docker while cleaning job: " + found.stderr)
        for container in found.stdout.split():
            subprocess.run(["docker", "rm", "-f", container], capture_output=True, timeout=20, check=True)
    # Proxy is task-owned and uses a deterministic exact name.
    subprocess.run(["docker", "rm", "-f", "research-" + identity + "-proxy"], capture_output=True, timeout=20)
    subprocess.run(["docker", "network", "rm", "research-" + identity + "-internal"], capture_output=True, timeout=20)


@contextmanager
def coordinator_lock(directory):
    with (directory / "coordinator.lock").open("a") as handle:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RuntimeError("A coordinator already owns this queue") from error
        yield


async def terminate(process):
    if process.returncode is None:
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            await asyncio.wait_for(process.wait(), 15)
        except asyncio.TimeoutError:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            await process.wait()


async def coordinate(directory, command, *, cleanup=cleanup_containers):
    """The command factory is injectable for complete offline integration tests."""
    check_plan(directory)
    plan = read(directory / "plan.json")
    with coordinator_lock(directory):
        queue = Queue(directory)
        active = {}
        running = set()
        try:
            # A crashed coordinator never silently replays a partly completed proof.
            for row in queue.rows():
                if row["state"] == "running":
                    job = next(job for job in plan["jobs"] if job["job_id"] == row["job_id"])
                    pid = row["pid"]
                    cmdline = Path(f"/proc/{pid}/cmdline")
                    if pid and cmdline.exists():
                        process_args = cmdline.read_bytes().split(b"\0")
                        if str(directory).encode() in process_args and job["job_id"].encode() in process_args:
                            try:
                                os.killpg(pid, signal.SIGKILL)
                            except ProcessLookupError:
                                pass
                    await asyncio.to_thread(cleanup, directory / job["directory"])
                    result = infrastructure(job, "Coordinator interrupted; partial evidence preserved; use a new experiment to retry")
                    atomic_json(directory / job["directory"] / "collected-result.json", result)
                    queue.finish(job["job_id"], result)

            async def launch(job):
                check_plan(directory)
                queue.claim(job["job_id"])
                root = directory / job["directory"]
                process = None
                try:
                    with (root / "worker.log").open("w") as log:
                        process = await asyncio.create_subprocess_exec(*command(job), stdout=log, stderr=asyncio.subprocess.STDOUT, start_new_session=True)
                        active[job["job_id"]] = (process, job)
                        queue.pid(job["job_id"], process.pid)
                        try:
                            code = await asyncio.wait_for(process.wait(), plan["limits"]["job_seconds"])
                        except asyncio.TimeoutError as error:
                            await terminate(process)
                            raise RuntimeError("Whole-job timeout") from error
                    value = validate_result(read(root / "result.json"), job)
                    if code != 0:
                        raise RuntimeError(f"Worker exited {code}; inspect worker.log")
                except (OSError, ValueError, KeyError, RuntimeError) as error:
                    value = infrastructure(job, error)
                finally:
                    if process is not None:
                        await terminate(process)
                    await asyncio.to_thread(cleanup, root)
                    active.pop(job["job_id"], None)
                atomic_json(root / "collected-result.json", value)
                queue.finish(job["job_id"], value)
                collect(directory, queue, plan)

            for mode in ("stateless", "retrieved"):
                pending = [job for job in plan["jobs"] if job["condition"] == mode and
                           next(row for row in queue.rows() if row["job_id"] == job["job_id"])["state"] == "queued"]
                running = set()
                while pending or running:
                    while pending and len(running) < plan["limits"]["jobs"]:
                        running.add(asyncio.create_task(launch(pending.pop(0))))
                    done, running = await asyncio.wait(running, return_when=asyncio.FIRST_COMPLETED)
                    for task in done:
                        task.result()
            collect(directory, queue, plan)
            return queue.rows()
        finally:
            for task in running:
                task.cancel()
            if running:
                await asyncio.gather(*running, return_exceptions=True)
            for process, job in list(active.values()):
                await terminate(process)
                await asyncio.to_thread(cleanup, directory / job["directory"])
            queue.close()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("plan", "run", "status", "search"))
    parser.add_argument("--spec", type=Path)
    parser.add_argument("--name")
    parser.add_argument("--experiment", type=Path)
    parser.add_argument("--query", help="Full-text query over collected run records and candidate lessons")
    parser.add_argument("--lean", type=Path, default=Path.home() / ".elan/toolchains/leanprover--lean4---v4.28.0")
    parser.add_argument("--packages", type=Path, default=ROOT / ".lake/packages")
    parser.add_argument("--auth", type=Path, default=Path(os.environ.get("RESEARCH_CODEX_AUTH", "/mnt/c/Users/austi/.codex/auth.json")))
    args = parser.parse_args(argv)
    if args.action == "plan":
        if not args.spec or not args.name:
            parser.error("plan requires --spec and --name")
        validate_name(args.name)
        directory = contained(ROOT / "experiments", args.name)
        plan = prepare(args.spec, directory)
        print(f"Frozen {len(plan['jobs'])} jobs at {directory}; no model calls made")
        return
    if not args.experiment:
        parser.error("run/status requires --experiment")
    directory = args.experiment.resolve()
    if not directory.is_relative_to(ROOT / "experiments"):
        raise ValueError("Batch must be under experiments/")
    check_plan(directory)
    archived = directory / "runtime-source/pipeline/batch.py"
    if args.action == "run" and Path(__file__).resolve() != archived.resolve():
        # Freeze the scheduler as well as the worker; don't mix future host
        # implementations with this experiment's original execution policy.
        forwarded = list(argv) if argv is not None else sys.argv[1:]
        result = subprocess.run([sys.executable, str(archived), *forwarded])
        if result.returncode:
            raise RuntimeError(f"Archived coordinator exited {result.returncode}")
        return
    if args.action == "search":
        if not args.query:
            parser.error("search requires --query")
        queue = Queue(directory)
        try:
            for job_id, snippet in queue.search(args.query):
                print(job_id + ": " + snippet)
        finally:
            queue.close()
        return
    if args.action == "status":
        queue = Queue(directory)
        try:
            for row in queue.rows():
                job = next(item for item in read(directory / "plan.json")["jobs"] if item["job_id"] == row["job_id"])
                heartbeat = directory / job["directory"] / "heartbeat.json"
                detail = ""
                if row["state"] == "running" and heartbeat.exists():
                    beat = read(heartbeat)
                    detail = f" stage={beat['stage']} heartbeat_age={time.time()-beat['unix']:.1f}s"
                if row["result"]:
                    detail = " outcome=" + json.loads(row["result"])["outcome"]
                print(f"{row['job_id']}: {row['state']}{detail}")
        finally:
            queue.close()
        return
    worker = directory / "runtime-source/pipeline/worker.py"
    def command(job):
        return [sys.executable, str(worker), "--batch", str(directory), "--job", job["job_id"],
                "--lean", str(args.lean.resolve()), "--packages", str(args.packages.resolve()), "--auth", str(args.auth.resolve())]
    result = asyncio.run(coordinate(directory, command))
    print(f"Finished {len(result)} jobs; comparison: {directory / 'comparison.json'}")
    if any(json.loads(row["result"])["outcome"] == "infrastructure_error" for row in result):
        raise RuntimeError("Infrastructure errors preserved; inspect status and worker logs")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, RuntimeError, sqlite3.Error) as error:
        print("ERROR:", error, file=sys.stderr)
        sys.exit(1)
