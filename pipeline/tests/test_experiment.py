"""Migration and isolation tests; no model calls or Docker required."""
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest
from unittest.mock import patch

PIPELINE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PIPELINE))
SPEC = importlib.util.spec_from_file_location("research_runner", PIPELINE / "run.py")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)
from engine import Engine

EXPERIMENT = runner.ROOT / "experiments/exp-001-binary-tree"


def config():
    return {"name": "test", "task_id": "test-task", "model": "test-model", "reasoning_effort": "medium",
            "conditions": ["stateless", "retrieved"], "inputs": "inputs", "memory": "memory",
            "evaluator": "evaluator", "image": "test-image", "builder_seconds": 1200,
            "critic_seconds": 300, "resources": {"memory": "8g", "cpus": 2, "pids": 256}}


class RunnerTests(unittest.TestCase):
    def test_historical_records_unchanged(self):
        directory, settings = runner.load_config(EXPERIMENT / "experiment.json")
        self.assertEqual(runner.check_experiment(directory, settings)["model"], "gpt-6.1-sol")

    def test_changed_frozen_input_rejected(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            (root / "input.txt").write_text("changed")
            (root / "frozen-manifest.json").write_text(json.dumps({"hashes": {"input.txt": "wrong"}}))
            with patch.object(runner, "ROOT", root):
                with self.assertRaisesRegex(RuntimeError, "Frozen input changed"):
                    runner.checked_record(root)

    def test_manifest_tampering_rejected(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            (root / "frozen-manifest.json").write_text('{"hashes": {}}')
            relocation = {"manifests": {"frozen-manifest.json": "wrong"}}
            with patch.object(runner, "ROOT", root):
                with self.assertRaisesRegex(RuntimeError, "Historical manifest changed"):
                    runner.checked_record(root, relocation)

    def test_existing_experiment_not_overwritten(self):
        with TemporaryDirectory() as folder:
            with self.assertRaises(FileExistsError):
                runner.initialize(Path(folder), Path(folder), {}, replay=False)

    def test_name_traversal_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "name must"):
            runner.validate_name("../escape")

    def initialize_fixture(self, replay):
        with TemporaryDirectory() as folder:
            root, settings = Path(folder), config()
            source, target = root / "source", root / "target"
            for name in ("inputs", "memory", "evaluator"):
                (source / name).mkdir(parents=True)
            for name in runner.CONFIG_FILES:
                (source / "evaluator" / name).write_text("protected config")
            (source / "frozen-manifest.json").write_text("{}")
            for condition in settings["conditions"]:
                actor = source / condition / "workspace/Research"
                actor.mkdir(parents=True)
                (actor / "Submission.lean").write_text("-- prior answer\n")
                (source / condition / "private-transcript.txt").write_text("must not copy")
            with patch.object(runner, "ROOT", root), patch.object(runner, "PIPELINE", root / "tools"), \
                 patch.object(runner.subprocess, "run", return_value=SimpleNamespace(stdout="test-commit")):
                current = runner.initialize(target, source, settings, replay)
            for condition in settings["conditions"]:
                text = (target / condition / "workspace/Research/Submission.lean").read_text()
                self.assertEqual(text, "-- prior answer\n" if replay else "import Mathlib\n")
                self.assertFalse((target / condition / "private-transcript.txt").exists())
            self.assertTrue((target / "artifacts").is_dir())
            self.assertTrue((target / "artifacts/index.md").is_file())
            self.assertEqual(current["name"], "target")
            self.assertNotIn("relocation", current)
            manifest = json.loads((target / "frozen-manifest.json").read_text())
            self.assertEqual(manifest["mode"], "offline-replay" if replay else "fresh-pair")
            with patch.object(runner, "ROOT", root):
                runner.checked_record(target)

    def test_fresh_builder_has_no_prior_answer(self):
        self.initialize_fixture(replay=False)

    def test_replay_copies_sources_not_transcripts(self):
        self.initialize_fixture(replay=True)

    def test_symlink_rejected(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            (root / "original").write_text("data")
            (root / "link").symlink_to(root / "original")
            with self.assertRaisesRegex(RuntimeError, "Unsafe path"):
                runner.contained(root, "link")

    def test_config_overlap_rejected(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            directory = root / "experiments/example"
            for name in ("inputs", "memory"):
                (directory / name).mkdir(parents=True)
            settings = config()
            settings["evaluator"] = "inputs"
            (directory / "experiment.json").write_text(json.dumps(settings))
            with patch.object(runner, "ROOT", root):
                with self.assertRaisesRegex(RuntimeError, "must be separate"):
                    runner.load_config(directory / "experiment.json")

    def container_args(self, condition, **kwargs):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            packages = root / "packages"
            (packages / "mathlib").mkdir(parents=True)
            engine = Engine(root / "example", config(), root / "lean", packages, root / "secret-auth.json", lambda: None)
            return " ".join(engine.container(condition, **kwargs))

    def test_stateless_has_no_memory_mount(self):
        args = self.container_args("stateless")
        self.assertNotIn("target=/memory", args)
        self.assertNotIn("target=/var/run/docker.sock", args)
        self.assertIn("--read-only --cap-drop=ALL", args)
        self.assertIn("target=/spec,readonly", args)
        self.assertIn("target=/workspace/Research.lean,readonly", args)

    def test_retrieved_memory_is_read_only(self):
        self.assertIn("target=/memory,readonly", self.container_args("retrieved"))

    def test_critic_has_read_only_candidate_without_memory(self):
        args = self.container_args("retrieved", reviewer=True)
        self.assertIn("target=/workspace,readonly", args)
        self.assertNotIn("target=/memory", args)

    def test_offline_has_no_network_credentials_or_memory(self):
        args = self.container_args("retrieved", offline=True)
        self.assertIn("--network none", args)
        self.assertNotIn("secret-auth", args)
        self.assertNotIn("target=/memory", args)

    def test_failed_gate_cannot_be_success(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            path = root / "stateless/evaluation"
            path.mkdir(parents=True)
            (path / "verification.json").write_text('{"formal_gate_passed": false}')
            with self.assertRaisesRegex(RuntimeError, "Formal gate failed"):
                runner.require_success(root, config(), semantic=False)

    def test_critic_failure_cannot_be_success(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            for directory in ("evaluation", "review"):
                (root / "stateless" / directory).mkdir(parents=True)
            (root / "stateless/evaluation/verification.json").write_text('{"formal_gate_passed": true}')
            (root / "stateless/review/review.json").write_text('{"overall_verdict": "uncertain"}')
            with self.assertRaises((RuntimeError, ValueError)):
                runner.require_success(root, config(), semantic=True)

    def test_navigation_links_exist(self):
        documents = [runner.ROOT / "README.md", EXPERIMENT / "artifacts/index.md",
                     runner.ROOT / "experiments/README.md", PIPELINE / "README.md",
                     PIPELINE / "REPRODUCE.md", EXPERIMENT / "README.md", EXPERIMENT / "REPORT.md",
                     *(EXPERIMENT / "artifacts").rglob("*.md"),
                     *(EXPERIMENT / "notes").glob("*.md"),
                     runner.ROOT / "experiments/dot_product/README.md"]
        for document in documents:
            for target in re.findall(r"\]\(([^)]+)\)", document.read_text()):
                if "://" in target or target.startswith("#"):
                    continue
                self.assertTrue((document.parent / target.split("#")[0]).exists(), f"{document}: {target}")

    def test_raw_evidence_preserved_byte_for_byte(self):
        relocation = json.loads((EXPERIMENT / "relocation.json").read_text())
        tree = subprocess.run(["git", "-C", str(runner.ROOT), "ls-tree", "-r", relocation["evidence_commit"],
                               "--", "experiments/memory-ablation"], check=True, capture_output=True, text=True).stdout
        checked = 0
        for line in tree.splitlines():
            metadata, old = line.split("\t", 1)
            if Path(old).name in ("README.md", "REPORT.md"):
                continue  # Navigation prose intentionally updated, not raw evidence.
            mapped = old
            for prefix, new in sorted(relocation["paths"].items(), key=lambda pair: -len(pair[0])):
                if old.startswith(prefix + "/"):
                    mapped = new + old[len(prefix):]
                    break
            actual = subprocess.run(["git", "-C", str(runner.ROOT), "hash-object", mapped],
                                    check=True, capture_output=True, text=True).stdout.strip()
            self.assertEqual(actual, metadata.split()[2], old)
            checked += 1
        self.assertGreater(checked, 100)

    def test_no_separate_root_project_or_artifact_stores(self):
        for name in ("projects", "artifacts", "Research", "Research.lean", "output"):
            self.assertFalse((runner.ROOT / name).exists(), name)

    def test_library_sources_preserved_byte_for_byte(self):
        before = "bf9b1d012f5a20d1e932d79d5d86a0709f25e69c"
        tree = subprocess.run(["git", "-C", str(runner.ROOT), "ls-tree", "-r", before,
                               "--", "Research", "Research.lean"], check=True, capture_output=True, text=True).stdout
        checked = 0
        for line in tree.splitlines():
            metadata, old = line.split("\t", 1)
            actual = subprocess.run(["git", "-C", str(runner.ROOT), "hash-object", "lean/" + old],
                                    check=True, capture_output=True, text=True).stdout.strip()
            self.assertEqual(actual, metadata.split()[2], old)
            checked += 1
        self.assertGreater(checked, 5)

    def test_presentation_deliverables_preserved(self):
        before = "bf9b1d012f5a20d1e932d79d5d86a0709f25e69c"
        tree = subprocess.run(["git", "-C", str(runner.ROOT), "ls-tree", "-r", before,
                               "--", "output/slides"], check=True, capture_output=True, text=True).stdout
        self.assertEqual(len(tree.splitlines()), 4)
        for line in tree.splitlines():
            metadata, old = line.split("\t", 1)
            path = EXPERIMENT / "presentations" / Path(old).name
            actual = subprocess.run(["git", "-C", str(runner.ROOT), "hash-object", str(path)],
                                    check=True, capture_output=True, text=True).stdout.strip()
            self.assertEqual(actual, metadata.split()[2], old)

    def verifier_fixture(self, source_dir, text, expected):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            binaries = root / "bin"
            binaries.mkdir()
            lake = binaries / "lake"
            lake.write_text("#!/bin/sh\nexit 0\n")
            lake.chmod(0o755)
            if source_dir:
                source = root / source_dir
                source.mkdir(parents=True)
                (source / "Check.lean").write_text(text)
            environment = dict(os.environ, PATH=str(binaries) + os.pathsep + os.environ["PATH"])
            result = subprocess.run(["bash", str(PIPELINE / "verify.sh")], cwd=root, env=environment,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, expected, result.stdout + result.stderr)

    def test_verifier_accepts_both_source_layouts(self):
        for source in ("lean/Research", "Research"):
            with self.subTest(source=source):
                self.verifier_fixture(source, "example : True := trivial\n", 0)

    def test_verifier_rejects_placeholder_and_axiom(self):
        for text in ("example : True := sorry\n", "axiom bad : False\n"):
            with self.subTest(text=text):
                self.verifier_fixture("lean/Research", text, 1)

    def test_verifier_fails_when_source_directory_is_missing(self):
        self.verifier_fixture(None, "", 1)


if __name__ == "__main__":
    unittest.main()
