"""Linux process-shared resource leases; workers never update the shared queue."""
from contextlib import contextmanager
import fcntl
import json
import os
from pathlib import Path
import threading
import time


def atomic_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + f".{os.getpid()}.tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


class ResourcePool:
    def __init__(self, directory, limits):
        self.directory, self.limits = Path(directory), limits
        self.directory.mkdir(parents=True, exist_ok=True)

    @contextmanager
    def lease(self, resource):
        handle = None
        while handle is None:
            for slot in range(self.limits[resource]):
                candidate = (self.directory / f"{resource}-{slot}.lock").open("a")
                try:
                    fcntl.flock(candidate, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    handle = candidate
                    break
                except BlockingIOError:
                    candidate.close()
            if handle is None:
                time.sleep(0.1)
        try:
            yield
        finally:
            fcntl.flock(handle, fcntl.LOCK_UN)
            handle.close()

    @contextmanager
    def stage(self, name):
        # Agents can run Lean, so reserve a build slot throughout model calls.
        # Acquire model before Lean consistently to avoid lock-order deadlocks.
        if name in ("builder", "critic", "connectivity"):
            with self.lease("model_calls"), self.lease("lean_builds"):
                yield
        else:
            with self.lease("lean_builds"):
                yield


class Heartbeat:
    def __init__(self, path, job_id, interval=2):
        self.path, self.job_id, self.interval = Path(path), job_id, interval
        self.current = "starting"
        self.stop = threading.Event()
        self.thread = threading.Thread(target=self.loop, daemon=True)

    def publish(self):
        atomic_json(self.path, {"job_id": self.job_id, "pid": os.getpid(),
                               "stage": self.current, "unix": time.time()})

    def loop(self):
        while not self.stop.wait(self.interval):
            self.publish()

    def __enter__(self):
        self.publish()
        self.thread.start()
        return self

    def __exit__(self, *args):
        self.stop.set()
        self.thread.join()

    @contextmanager
    def stage(self, pool, name):
        self.current = "waiting:" + name
        with pool.stage(name):
            self.current = name
            try:
                yield
            finally:
                self.current = "between-stages"
