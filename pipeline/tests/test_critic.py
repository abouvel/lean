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
            session.assert_called_once_with("rubric", kind="reviewer")

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
                    with self.assertRaises(RuntimeError):
                        critic.require_pass(directory)
            (directory / "review.json").write_text("not json")
            with self.assertRaises(ValueError):
                critic.require_pass(directory)

    def test_verdict_gate_accepts_pass(self):
        with TemporaryDirectory() as folder:
            directory = Path(folder)
            (directory / "review.json").write_text('{"overall_verdict": "pass"}')
            critic.require_pass(directory)

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
