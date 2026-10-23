"""Critic module tests: no Docker engine or model calls."""
import contextlib
import io
import json
import os
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

PIPELINE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PIPELINE))
import agent
import critic
from engine import Engine

EXPERIMENT = PIPELINE.parent / "experiments/exp-001-binary-tree"


class CriticTests(unittest.TestCase):
    def make_engine(self, root):
        settings = json.loads((EXPERIMENT / "experiment.json").read_text())
        for folder in ("inputs", "evaluator", "packages/mathlib"):
            (root / folder).mkdir(parents=True)
        for name in ("source.txt", "source.pdf"):
            (root / "inputs" / name).write_text("original source")
        (root / "inputs/PROMPT.txt").write_text("builder assignment, not critic input")
        (root / "evaluator/REVIEWER.txt").write_text("critic rubric")
        for condition in settings["conditions"]:
            (root / condition / "evaluation-workspace").mkdir(parents=True)
            (root / condition / "evaluation").mkdir()
        engine = Engine(root, settings, root / "lean", root / "packages", root / "auth.json", Mock())
        engine.network = Mock()
        return engine

    def test_review_launches_separate_critic_entry_point_with_restricted_mounts(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            engine = self.make_engine(root)
            with patch("critic.subprocess.run", return_value=SimpleNamespace(returncode=0)) as process:
                critic.review(engine)
            engine.guard.assert_called_once_with()
            engine.network.assert_called_once_with()
            self.assertEqual(process.call_count, 2)
            for condition, invocation in zip(engine.conditions, process.call_args_list):
                command = invocation.args[0]
                mounts = " ".join(command)
                self.assertEqual(command[-2:], ["python3", "/runner/critic.py"])
                self.assertIn("target=/runner/critic.py,readonly", mounts)
                self.assertIn("target=/runner/agent.py,readonly", mounts)
                self.assertIn("target=/workspace,readonly", mounts)
                self.assertIn("target=/evaluation,readonly", mounts)
                self.assertNotIn("target=/memory", mounts)
                self.assertEqual(invocation.kwargs["timeout"], engine.config["critic_seconds"] + 60)
                spec = root / condition / "reviewer-spec"
                self.assertEqual({p.name for p in spec.iterdir()}, {"source.txt", "source.pdf", "REVIEWER.txt"})
                self.assertEqual((spec / "REVIEWER.txt").read_text(), "critic rubric")
                self.assertFalse((spec / "PROMPT.txt").exists())

    def test_existing_review_not_overwritten(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            engine = self.make_engine(root)
            (root / "stateless/reviewer-spec").mkdir(parents=True)
            with patch("critic.subprocess.run") as process:
                with self.assertRaises(FileExistsError):
                    critic.review(engine)
                process.assert_not_called()

    def test_frozen_input_guard_runs_before_launch(self):
        with TemporaryDirectory() as folder:
            engine = self.make_engine(Path(folder))
            engine.guard.side_effect = RuntimeError("inputs changed")
            with patch("critic.subprocess.run") as process:
                with self.assertRaisesRegex(RuntimeError, "inputs changed"):
                    critic.review(engine)
                process.assert_not_called()
            engine.network.assert_not_called()

    def test_critic_entry_point_has_explicit_reviewer_role(self):
        with patch("critic.reviewer_prompt", return_value="rubric"), patch("critic.run_agent") as session:
            critic.main()
            self.assertEqual(session.call_args.args[0], critic.COMPLETENESS_FIRST + "rubric")
            self.assertEqual(session.call_args.kwargs["kind"], "reviewer")
            self.assertTrue(callable(session.call_args.kwargs["stop_when"]))

    def test_builder_entry_point_has_explicit_builder_role(self):
        with patch("agent.builder_prompt", return_value="assignment"), patch("agent.run_agent") as session:
            agent.main()
            session.assert_called_once_with("assignment", kind="builder")

    def test_frozen_prompts_are_unchanged_by_extraction(self):
        for condition in ("stateless", "retrieved"):
            with self.subTest(condition=condition):
                self.assertEqual(agent.builder_prompt(EXPERIMENT / "inputs", condition=condition),
                                 (EXPERIMENT / condition / "output/actual-prompt.txt").read_text())
                self.assertEqual(critic.reviewer_prompt(EXPERIMENT / "evaluator"),
                                 (EXPERIMENT / condition / "review/actual-prompt.txt").read_text())

    def test_verdict_gate_rejects_nonpass_and_malformed_reports(self):
        with TemporaryDirectory() as folder:
            directory = Path(folder)
            for report in ({"overall_verdict": "fail"}, {"overall_verdict": "uncertain"}, {}, [], "pass"):
                with self.subTest(report=report):
                    (directory / "review.json").write_text(json.dumps(report))
                    with self.assertRaises((RuntimeError, ValueError)):
                        critic.require_pass(directory)
            (directory / "review.json").write_text("not json")
            with self.assertRaises(ValueError):
                critic.require_pass(directory)

    def test_verdict_gate_accepts_pass(self):
        with TemporaryDirectory() as folder:
            directory = Path(folder)
            (directory / "review.json").write_text(json.dumps(self.report("pass", "final")))
            critic.require_pass(directory)

    def report(self, verdict="fail", phase="completeness"):
        return {"overall_verdict": verdict, "phase": phase,
                "target_evidence": "Submission.lean:12 defines a proposition but never proves it",
                "requirements": [{"requirement": "Prove the full bound", "evidence": "Submission.lean:12",
                                  "verdict": verdict, "correction": "Prove the bound under the original assumptions"}],
                "assumptions_added": [], "missing_obligations": [] if verdict == "pass" else ["Full bound"],
                "limitations": []}

    def test_only_definite_valid_rejection_stops_critic(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            for report in (self.report("pass"), self.report("uncertain"), {}, self.report("fail", "final")):
                (root / "checkpoint.json").write_text(json.dumps(report))
                self.assertFalse(critic.rejection_checkpoint(root))
            (root / "checkpoint.json").write_text('{"overall_verdict":')
            self.assertFalse(critic.rejection_checkpoint(root))
            (root / "checkpoint.json").write_text(json.dumps(self.report()))
            self.assertTrue(critic.rejection_checkpoint(root))

    def test_checkpoint_failure_can_be_feedback_but_timeout_cannot(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            (root / "checkpoint.json").write_text(json.dumps(self.report()))
            metrics = {"exit_code": -15, "timed_out": False, "stopped_for_checkpoint": True}
            self.assertEqual(critic.completed_review(root, metrics)["overall_verdict"], "fail")
            for changes in ({"timed_out": True}, {"stopped_for_checkpoint": False}):
                with self.assertRaises(RuntimeError):
                    critic.completed_review(root, dict(metrics, **changes))

    def test_pass_requires_final_target_evidence_and_no_missing_obligations(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            for changes in ({"target_evidence": ""}, {"phase": "completeness"},
                            {"missing_obligations": ["Bound"]}, {"requirements": []}):
                (root / "review.json").write_text(json.dumps(dict(self.report("pass", "final"), **changes)))
                with self.assertRaises(ValueError):
                    critic.require_pass(root)

    def test_session_stops_on_checkpoint_without_marking_timeout(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            environment = {"CODEX_HOME": str(root / "home"), "EXPERIMENT_MODEL": "test",
                           "REASONING_EFFORT": "medium", "TIME_LIMIT_SECONDS": "120"}
            process = Mock(returncode=-15)
            process.communicate.side_effect = agent.subprocess.TimeoutExpired("codex", 2)
            with patch.dict(os.environ, environment), patch("agent.subprocess.Popen", return_value=process), \
                 contextlib.redirect_stdout(io.StringIO()):
                result = agent.run_agent("rubric", kind="reviewer", output=root / "output", stop_when=lambda: True)
            process.terminate.assert_called_once()
            self.assertTrue(result["stopped_for_checkpoint"])
            self.assertFalse(result["timed_out"])

    def test_uncertain_checkpoint_does_not_extend_time_budget(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            environment = {"CODEX_HOME": str(root / "home"), "EXPERIMENT_MODEL": "test",
                           "REASONING_EFFORT": "medium", "TIME_LIMIT_SECONDS": "3"}
            process = Mock(returncode=-15)
            process.communicate.side_effect = agent.subprocess.TimeoutExpired("codex", 2)
            with patch.dict(os.environ, environment), patch("agent.subprocess.Popen", return_value=process), \
                 patch("agent.time.monotonic", side_effect=[0, 0, 3]), contextlib.redirect_stdout(io.StringIO()):
                result = agent.run_agent("rubric", kind="reviewer", output=root / "output", stop_when=lambda: False)
            self.assertTrue(result["timed_out"])
            self.assertFalse(result.get("stopped_for_checkpoint", False))

    def test_controller_returns_checkpoint_rejection_to_repair_loop(self):
        from passes import execute
        with TemporaryDirectory() as folder:
            root = Path(folder)
            for name in ("output", "evaluation", "review"):
                (root / "stateless" / name).mkdir(parents=True)
            (root / "stateless/output/metrics.json").write_text('{"exit_code": 0}')
            (root / "stateless/evaluation/verification.json").write_text('{"formal_gate_passed": true}')
            (root / "stateless/review/metrics.json").write_text(json.dumps(
                {"exit_code": -15, "timed_out": False, "stopped_for_checkpoint": True}))
            (root / "stateless/review/checkpoint.json").write_text(json.dumps(self.report()))
            child = SimpleNamespace(directory=root, builders=Mock(), evaluate=Mock())
            with patch("passes.review"):
                result = execute(child, "stateless")
            self.assertEqual(result["status"], "critic_failed")
            self.assertIn("Full bound", result["report"]["missing_obligations"])

    def test_archived_runtime_is_hash_checked_without_relaxing_task_checks(self):
        import run as runner
        with TemporaryDirectory() as folder:
            root = Path(folder)
            (root / "pipeline").mkdir()
            (root / "pipeline/critic.py").write_text("new critic")
            archive = root / "runtime-source/pipeline"
            archive.mkdir(parents=True)
            (archive / "critic.py").write_text("original critic")
            (root / "task.txt").write_text("original task")
            hashes = {"pipeline/critic.py": runner.digest(archive / "critic.py"),
                      "task.txt": runner.digest(root / "task.txt")}
            (root / "frozen-manifest.json").write_text(json.dumps({"hashes": hashes}))
            with patch.object(runner, "ROOT", root):
                runner.checked_record(root)
                (root / "task.txt").write_text("changed task")
                with self.assertRaisesRegex(RuntimeError, "task.txt"):
                    runner.checked_record(root)
                (root / "task.txt").write_text("original task")
                (archive / "critic.py").write_text("corrupted archive")
                with self.assertRaisesRegex(RuntimeError, "pipeline/critic.py"):
                    runner.checked_record(root)

    def test_shared_session_records_reviewer_metadata_without_adding_memory_prompt(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            environment = {"CODEX_HOME": str(root / "home"), "MEMORY_MODE": "retrieved",
                           "EXPERIMENT_MODEL": "test-model", "REASONING_EFFORT": "medium",
                           "TIME_LIMIT_SECONDS": "300"}
            process = Mock(returncode=0)
            with patch.dict(os.environ, environment), patch("agent.subprocess.Popen", return_value=process) as launch, \
                 contextlib.redirect_stdout(io.StringIO()):
                result = agent.run_agent("critic rubric", kind="reviewer", output=root / "output")
            process.communicate.assert_called_once_with("critic rubric", timeout=300)
            self.assertIn("--ephemeral", launch.call_args.args[0])
            self.assertEqual(result["kind"], "reviewer")
            self.assertEqual(result["time_limit_seconds"], 300)
            self.assertEqual(result["token_usage"], "unknown")
            self.assertEqual((root / "output/actual-prompt.txt").read_text(), "critic rubric")
            self.assertTrue((root / "output/metrics.json").is_file())


if __name__ == "__main__":
    unittest.main()
