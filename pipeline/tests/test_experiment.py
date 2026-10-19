"""Runner safety tests; no Docker, credentials, or model calls required."""
import importlib.util
import json
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest
from unittest.mock import patch

MODULE = Path(__file__).resolve().parents[1] / "experiment.py"
SPEC = importlib.util.spec_from_file_location("experiment", MODULE)
experiment = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(experiment)


class RunnerTests(unittest.TestCase):
    def test_historical_inputs_unchanged(self):
        self.assertEqual(experiment.checked_template(experiment.DEFAULT)["model"], "gpt-6.1-sol")

    def test_existing_run_id_rejected(self):
        with TemporaryDirectory() as folder:
            target = Path(folder)
            with self.assertRaises(FileExistsError):
                experiment.initialize(SimpleNamespace(RUN=target), target, {}, replay=False)

    def test_invalid_id_rejected(self):
        args = SimpleNamespace(lean=Path("."), packages=Path("."), auth=Path("."), run_id="../escape")
        with self.assertRaisesRegex(RuntimeError, "run-id"):
            experiment.configure(args, {"model": "test", "reasoning_effort": "medium"})

    def test_changed_frozen_input_rejected(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            (root / "input.txt").write_text("changed")
            (root / "frozen-manifest.json").write_text(json.dumps({"hashes": {"input.txt": "wrong"}}))
            with patch.object(experiment, "ROOT", root):
                with self.assertRaisesRegex(RuntimeError, "Frozen input changed"):
                    experiment.checked_template(root)

    def initialize_fixture(self, replay):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            template = root / "template"
            tools = root / "tools"
            tools.mkdir()
            for directory in ("spec", "memory", "trusted"):
                (template / directory).mkdir(parents=True)
            for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "Research.lean"):
                (template / "trusted" / name).write_text("protected config")
            (template / "frozen-manifest.json").write_text("{}")
            for condition in ("stateless", "retrieved"):
                source = template / condition / "workspace/Research"
                source.mkdir(parents=True)
                (source / "Submission.lean").write_text("-- prior completed answer\n")
            def save(path, value):
                path.write_text(json.dumps(value) if isinstance(value, dict) else value)
            engine = SimpleNamespace(RUN=root / "new", CONDITIONS=("stateless", "retrieved"),
                                     ownership=lambda path: None, save=save,
                                     digest=lambda path: "test-hash",
                                     call=lambda command: SimpleNamespace(stdout="test-commit"))
            with patch.object(experiment, "ROOT", root), patch.object(experiment, "ENGINE", tools), \
                 patch.object(experiment, "__file__", str(root / "experiment.py")):
                experiment.initialize(engine, template, {}, replay)
            for condition in engine.CONDITIONS:
                text = (engine.RUN / condition / "workspace/Research/Submission.lean").read_text()
                self.assertEqual(text, "-- prior completed answer\n" if replay else "import Mathlib\n")
            self.assertEqual(json.loads((engine.RUN / "frozen-manifest.json").read_text())["mode"],
                             "offline-replay" if replay else "fresh-pair")

    def test_fresh_builders_receive_no_previous_answer(self):
        self.initialize_fixture(replay=False)

    def test_replay_copies_saved_sources(self):
        self.initialize_fixture(replay=True)

    def test_failed_formal_gate_is_not_success(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            for condition in ("stateless", "retrieved"):
                path = root / condition / "evaluation"
                path.mkdir(parents=True)
                (path / "verification.json").write_text('{"formal_gate_passed": false}')
            with self.assertRaisesRegex(RuntimeError, "formal gate failed"):
                experiment.formal_results(SimpleNamespace(RUN=root, CONDITIONS=("stateless", "retrieved")))


if __name__ == "__main__":
    unittest.main()
