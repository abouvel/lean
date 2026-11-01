"""Prove leases bound real concurrent processes and release after process death."""
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
import unittest

PIPELINE = Path(__file__).resolve().parents[1]
SCRIPT = '''
import json, pathlib, sys, time
sys.path.insert(0, sys.argv[1])
from resources import ResourcePool
root, name = pathlib.Path(sys.argv[2]), sys.argv[3]
pool = ResourcePool(root / "leases", {"model_calls": 1, "lean_builds": 2})
with pool.stage(name):
    with (root / "trace.jsonl").open("a") as out:
        out.write(json.dumps({"event": "start", "time": time.monotonic()}) + "\\n")
    time.sleep(0.15)
    with (root / "trace.jsonl").open("a") as out:
        out.write(json.dumps({"event": "end", "time": time.monotonic()}) + "\\n")
'''


class ResourceTests(unittest.TestCase):
    def test_model_and_lean_limits_apply_across_processes(self):
        for stage, expected in (("builder", 1), ("verification", 2)):
            with self.subTest(stage=stage), TemporaryDirectory() as folder:
                processes = [subprocess.Popen([sys.executable, "-c", SCRIPT, str(PIPELINE), folder, stage]) for _ in range(4)]
                for process in processes:
                    self.assertEqual(process.wait(timeout=10), 0)
                events = [json.loads(line) for line in (Path(folder) / "trace.jsonl").read_text().splitlines()]
                live = maximum = 0
                for event in sorted(events, key=lambda item: item["time"]):
                    live += 1 if event["event"] == "start" else -1
                    maximum = max(maximum, live)
                self.assertEqual(maximum, expected)


if __name__ == "__main__":
    unittest.main()
