"""Exercise bounded feedback and artifact accounting without models or Docker."""
import json
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest
from unittest.mock import Mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from passes import run_pair, make_pass
from artifacts import validate
from engine import CONFIG_FILES, save


class PassTests(unittest.TestCase):
    def fixture(self, root):
        config = {"inputs": "inputs", "memory": "memory", "evaluator": "evaluator", "max_passes": 2,
                  "conditions": ["stateless", "retrieved"], "model": "test", "reasoning_effort": "medium",
                  "builder_seconds": 3, "critic_seconds": 2, "task_id": "test", "image": "test"}
        for key in ("inputs", "memory", "evaluator"):
            (root / key).mkdir()
        (root / "inputs/PROMPT.txt").write_text("assignment")
        (root / "evaluator/REVIEWER.txt").write_text("rubric")
        for name in CONFIG_FILES:
            (root / "evaluator" / name).write_text("import Mathlib\n")
        save(root / "frozen-manifest.json", {"starting_commit": "test", "hashes": {}})
        return SimpleNamespace(directory=root, config=config, conditions=("stateless", "retrieved"),
                               lean=root / "lean", packages=root / "packages", auth=root / "auth",
                               guard=Mock(), net="test-net", proxy="test-proxy")

    def attempt(self, child, condition, status):
        path = child.directory / condition / "evaluation/verification.log"
        save(path, "exact diagnostic")
        return {"status": status, "builder": {"wall_time_seconds": 1, "compiler_command_events": 2},
                "verification": {"formal_gate_passed": status != "formal_failed"}, "critic": {},
                "report": {"requirements": []}}

    def test_same_budget_and_no_cross_condition_feedback(self):
        with TemporaryDirectory() as folder:
            parent = self.fixture(Path(folder))
            calls = []
            def attempt(child, condition):
                number = len([c for c in calls if c == condition]) + 1
                calls.append(condition)
                self.assertEqual(child.config["max_passes"], 2)
                if number == 1:
                    self.assertFalse((child.directory / "feedback").exists())
                else:
                    self.assertEqual(json.loads((child.directory / "feedback/feedback.json").read_text())["previous_pass"], 1)
                return self.attempt(child, condition, "formal_failed" if number == 1 else "accepted")
            result = run_pair(parent, attempt)
            self.assertEqual(calls, ["stateless", "stateless", "retrieved", "retrieved"])
            for record in result["conditions"].values():
                validate(record)
                self.assertEqual(record["metrics"]["passes_used"], 2)
                self.assertTrue(record["success"])
                self.assertFalse(record["reuse"]["approved"])
                self.assertEqual(record["metrics"]["builder_seconds"], 2)

    def test_stops_at_cap_and_preserves_failures(self):
        with TemporaryDirectory() as folder:
            parent = self.fixture(Path(folder))
            result = run_pair(parent, lambda child, condition: self.attempt(child, condition, "formal_failed"))
            for record in result["conditions"].values():
                self.assertFalse(record["success"])
                self.assertEqual(len(record["passes"]), 2)
                self.assertEqual(record["metrics"]["formal_failures"], 2)
            self.assertEqual(len(list((parent.directory / "artifacts").glob("*.json"))), 2)

    def test_infrastructure_failure_is_not_repaired_as_a_proof(self):
        with TemporaryDirectory() as folder:
            parent = self.fixture(Path(folder))
            def broken(child, condition):
                raise ValueError("invalid critic json")
            result = run_pair(parent, broken)
            for record in result["conditions"].values():
                self.assertEqual(record["outcome"], "infrastructure_error")
                self.assertEqual(len(record["passes"]), 1)

    def test_pass_inputs_cannot_change_after_freezing(self):
        with TemporaryDirectory() as folder:
            parent = self.fixture(Path(folder))
            child = make_pass(parent, "stateless", 1)
            child.guard()
            (child.directory / "inputs/PROMPT.txt").write_text("changed")
            with self.assertRaises(RuntimeError):
                child.guard()

    def test_success_stops_early_without_using_spare_passes(self):
        with TemporaryDirectory() as folder:
            parent = self.fixture(Path(folder))
            result = run_pair(parent, lambda child, condition: self.attempt(child, condition, "accepted"))
            self.assertTrue(all(len(record["passes"]) == 1 for record in result["conditions"].values()))

    def test_critic_feedback_repairs_only_own_candidate_without_private_evidence(self):
        with TemporaryDirectory() as folder:
            parent = self.fixture(Path(folder))
            def attempt(child, condition):
                source = child.directory / condition / "workspace/Research/Submission.lean"
                first = not (child.directory / "feedback").exists()
                result = self.attempt(child, condition, "critic_failed" if first else "accepted")
                if first:
                    self.assertEqual(source.read_text(), "import Mathlib\n")
                    source.write_text("-- own candidate: " + condition)
                    result["report"] = {"requirements": [{"requirement": "carry", "verdict": "fail",
                        "evidence": "private withheld case", "correction": "carry unchanged"}]}
                else:
                    self.assertEqual(source.read_text(), "-- own candidate: " + condition)
                    feedback = (child.directory / "feedback/feedback.json").read_text()
                    self.assertNotIn("private withheld case", feedback)
                    self.assertIn("carry unchanged", feedback)
                return result
            result = run_pair(parent, attempt)
            self.assertTrue(all(item["success"] for item in result["conditions"].values()))

    def test_uncertain_critic_stops_for_human(self):
        with TemporaryDirectory() as folder:
            parent = self.fixture(Path(folder))
            result = run_pair(parent, lambda child, condition: self.attempt(child, condition, "needs_human"))
            self.assertTrue(all(item["outcome"] == "needs_human" and len(item["passes"]) == 1
                                for item in result["conditions"].values()))


if __name__ == "__main__":
    unittest.main()
