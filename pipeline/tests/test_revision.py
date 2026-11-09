"""New acceptance boundaries: actual inputs, explicit handoffs, and fail-closed reports."""
import copy
import json
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from engine import Engine, CONFIG_FILES
from formal_context import parse_extraction, protected_declarations, translation_bundle, protected_sources
from roles import launch, handoff, validate_settings
from roundtrip import validate_translation, validate_judgment, route
from stages import execute
from formal_context import FormalizationFailure
from agent import export_permissions


def settings():
    return {"schema_version": 1, "mode": "calibration", "seconds": {
        role: 60 for role in ("planner", "formalizer", "prover", "translator", "judge")}}


def context():
    return {"schema_version": 1, "candidate_hash": "hash", "environment": {},
        "sources": {"Research/Submission.lean": "sourcehash"}, "axioms": [],
        "declarations": [
            {"name": "Research.claim", "module": "Research.Submission", "kind": "theorem", "type": "True", "body": ""},
            {"name": "Research.algorithm", "module": "Research.Submission", "kind": "definition", "type": "Nat", "body": "1"}]}


def bundle():
    return translation_bundle(context(), {"targets": ["Research.claim"], "construction_names": ["Research.algorithm"]})


def translation():
    return {"schema_version": 1, "candidate_hash": "hash", "status": "complete", "statement": "The claim is true.",
        "targets": [{"name": "Research.claim", "statement": "Truth holds."}],
        "constructions": [{"name": "Research.algorithm", "description": "The number one."}],
        "assumptions": [], "missing_context": []}


def catalog():
    return {"schema_version": 1, "requirements": [{"id": "target-completeness", "description": "Prove target"}],
        "defect_categories": [{"id": "missing-final-theorem", "description": "Missing target"}]}


def judgment(verdict="pass"):
    return {"schema_version": 2, "candidate_hash": "hash", "phase": "final", "overall_verdict": verdict,
        "delivery_complete": verdict == "pass", "construction_complete": True, "missing_formal_steps": [],
        "lean_implies_source": verdict == "pass", "source_implies_lean": True,
        "relation": "faithful" if verdict == "pass" else "mismatch", "target_evidence": "Translation target clause",
        "requirements": [{"requirement_id": "target-completeness", "requirement": "Prove target", "evidence": "Target clause",
            "verdict": verdict, "defect_categories": [] if verdict == "pass" else ["missing-final-theorem"],
            "correction": "" if verdict == "pass" else "Prove the target"}],
        "assumptions_added": [], "missing_obligations": [], "limitations": []}


class RevisionTests(unittest.TestCase):
    def test_final_formal_failure_preserves_invoked_role_accounting(self):
        engine = SimpleNamespace(config={"revision": settings()})
        invoked = {role: {"wall_time_seconds": 2} for role in ("planner", "formalizer", "prover")}
        with patch("stages.build", return_value={"roles": invoked}), patch("stages.verify",
                return_value={"formal_gate_passed": False}):
            result = execute(engine, "stateless")
        self.assertEqual(result["status"], "formal_failed")
        self.assertEqual(result["roles"], invoked)

    def test_atomic_private_files_export_with_readable_permissions(self):
        with TemporaryDirectory() as folder:
            root=Path(folder)
            private=root/"atomic-report.json"
            private.write_text("{}")
            private.chmod(0o600)
            export_permissions(root)
            self.assertEqual(private.stat().st_mode & 0o777,0o666)
            link=root/"outside"
            link.symlink_to(private)
            with self.assertRaisesRegex(RuntimeError,"symlink"):
                export_permissions(root)
    def test_formalizer_compile_failure_is_repairable_not_infrastructure(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            engine = SimpleNamespace(directory=root,config={"revision":settings()})
            with patch("stages.build",side_effect=FormalizationFailure("exact Lean diagnostic")):
                result=execute(engine,"stateless")
            self.assertEqual(result["status"],"formal_failed")
            self.assertFalse(result["verification"]["formal_gate_passed"])
            self.assertEqual((root/"stateless/evaluation/verification.log").read_text(),"exact Lean diagnostic")

    def test_proof_terms_or_duplicate_extraction_markers_rejected(self):
        value = context()
        text = "FORMAL_CONTEXT_JSON:" + json.dumps(value)
        self.assertEqual(len(parse_extraction(text)["declarations"]), 2)
        with self.assertRaises(ValueError):
            parse_extraction(text + "\n" + text)
        value["declarations"][0]["body"] = "a theorem proof"
        with self.assertRaisesRegex(ValueError, "proof leaked"):
            parse_extraction("FORMAL_CONTEXT_JSON:" + json.dumps(value))

    def test_only_formalizer_claims_are_protected_while_new_helpers_allowed(self):
        a, b = context(), context()
        b["declarations"].append({"name": "helper", "type": "True", "body": "", "kind": "theorem"})
        self.assertEqual(protected_declarations(a, b), [])
        b["declarations"][0]["type"] = "True -> True"
        self.assertEqual(protected_declarations(a, b), ["Research.claim"])
        b["declarations"][1]["body"] = "0"
        self.assertIn("Research.algorithm", protected_declarations(a, b))

    def test_bundle_has_no_source_paths_and_requires_actual_targets(self):
        value = bundle()
        self.assertNotIn("sources", value)
        self.assertNotIn("sourcehash", json.dumps(value))
        with self.assertRaisesRegex(ValueError, "not a theorem"):
            translation_bundle(context(), {"targets": ["Research.algorithm"], "construction_names": []})
        c = context()
        c["declarations"].append({"name":"unrelated_prompt","kind":"definition","type":"String",
            "module":"Research.Submission","body":"ORIGINAL_SECRET_TASK","dependencies":[]})
        blinded = translation_bundle(c,{"targets":["Research.claim"],"construction_names":["Research.algorithm"]})
        self.assertNotIn("ORIGINAL_SECRET_TASK", json.dumps(blinded))

    def test_bundle_includes_structure_and_constructor_but_rejects_theorem_or_missing_name(self):
        c = context()
        c["declarations"] += [
            {"name": "Research.Trace", "module": "Research.Submission", "kind": "inductive",
             "type": "Type", "body": "", "dependencies": ["Research.Trace.mk"]},
            {"name": "Research.Trace.mk", "module": "Research.Submission", "kind": "constructor",
             "type": "Nat → Research.Trace", "body": "", "dependencies": ["Research.Trace"]},
        ]
        result = translation_bundle(c, {"targets": ["Research.claim"],
                                        "construction_names": ["Research.Trace", "Research.algorithm"]})
        self.assertEqual({item["name"] for item in result["declarations"]},
                         {"Research.claim", "Research.algorithm", "Research.Trace", "Research.Trace.mk"})
        for invalid in ("Research.claim", "Research.Trace.mk", "Research.Missing"):
            with self.subTest(invalid=invalid), self.assertRaisesRegex(ValueError, "Construction"):
                translation_bundle(c, {"targets": ["Research.claim"], "construction_names": [invalid]})

    def test_translation_must_cover_exact_target_names_and_hash(self):
        for change in ("hash", "targets", "missing"):
            value = translation()
            if change == "hash": value["candidate_hash"] = "old"
            if change == "targets": value["targets"] = []
            if change == "missing": value["missing_context"] = ["definition unavailable"]
            with self.subTest(change=change), self.assertRaises(ValueError):
                validate_translation(value, bundle())

    def test_judgment_cannot_pass_with_missing_context_or_false_implication(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            for kind in ("valid", "missing", "hash", "implication", "assumptions", "delivery", "construction", "bridge"):
                value, tr = judgment(), translation()
                if kind == "missing": tr.update(status="insufficient_context", missing_context=["No definition"])
                if kind == "hash": value["candidate_hash"] = "old"
                if kind == "implication": value["lean_implies_source"] = False
                if kind == "assumptions": value["assumptions_added"] = ["rounding is exact"]
                if kind == "delivery": value["delivery_complete"] = False
                if kind == "construction": value["construction_complete"] = False
                if kind == "bridge": value["missing_formal_steps"] = ["Compose the two bounds in Lean"]
                (root / "roundtrip.json").write_text(json.dumps(value))
                if kind == "valid":
                    self.assertEqual(validate_judgment(root, bundle(), tr, catalog())["overall_verdict"], "pass")
                else:
                    with self.subTest(kind=kind), self.assertRaises(ValueError):
                        validate_judgment(root, bundle(), tr, catalog())

    def test_logical_implication_does_not_complete_missing_lean_delivery(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            value = judgment("fail")
            value.update(lean_implies_source=True, relation="faithful",
                missing_formal_steps=["Prove the composition of the component bounds"])
            (root / "roundtrip.json").write_text(json.dumps(value))
            self.assertEqual(validate_judgment(root, bundle(), translation(), catalog())["overall_verdict"], "fail")

    def test_calibration_disagreement_requires_human_without_mutating_raw_reports(self):
        a, b = judgment(), judgment("fail")
        saved = copy.deepcopy(b)
        status, report = route(a, b)
        self.assertEqual(status, "needs_human")
        self.assertEqual(report["overall_verdict"], "uncertain")
        self.assertEqual(b, saved)
        self.assertEqual(route(a, a)[0], "accepted")
        self.assertEqual(route(b, b)[0], "critic_failed")

    def engine(self, root):
        config = {"conditions": ["retrieved"], "revision": settings(), "inputs": "inputs", "memory": "memory",
            "evaluator": "evaluator", "model": "test", "reasoning_effort": "medium", "image": "test",
            "builder_seconds": 60, "critic_seconds": 60, "resources": {"pids": 16, "cpus": 1, "memory": "1g"}}
        for folder in ("inputs/support", "memory", "evaluator", "packages/mathlib", "retrieved/workspace"):
            (root / folder).mkdir(parents=True)
        (root / "inputs/source.txt").write_text("ORIGINAL_SECRET_TASK")
        (root / "inputs/PROMPT.txt").write_text("BUILDER_INSTRUCTIONS")
        (root / "memory/index.md").write_text("RESEARCH_MEMORY")
        for name in CONFIG_FILES:
            (root / "evaluator" / name).write_text("import Research.Submission\n")
        engine = Engine(root, config, root / "lean", root / "packages", root / "auth", Mock())
        engine.network = Mock()
        return engine

    def test_translator_and_judge_are_physically_blind_not_just_prompted(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            engine = self.engine(root)
            def process(command, **kwargs):
                role = "translator" if "RESEARCH_ROLE=translator" in command else "judge"
                out = root / "retrieved/roles" / role
                (out / "metrics.json").write_text('{"exit_code":0,"timed_out":false}')
                mounts = " ".join(command)
                self.assertNotIn("target=/memory", mounts)
                self.assertNotIn("target=/feedback", mounts)
                self.assertIn("MEMORY_MODE=blind", command)
                self.assertNotIn("MEMORY_MODE=retrieved", command)
                return SimpleNamespace(returncode=0)
            with patch("roles.subprocess.run", side_effect=process):
                launch(engine, "retrieved", "translator", "translate", payload={"formal-context.json": bundle()})
                launch(engine, "retrieved", "judge", "judge", payload={"translation.json": translation()},
                    files={"source.txt": root / "inputs/source.txt"})
            translator = root / "retrieved/role-spec/translator"
            self.assertEqual({p.name for p in translator.iterdir()}, {"ROLE.txt", "formal-context.json"})
            all_text = "".join(p.read_text() for p in translator.rglob("*") if p.is_file())
            self.assertNotIn("ORIGINAL_SECRET_TASK", all_text)
            self.assertNotIn("RESEARCH_MEMORY", all_text)
            self.assertNotIn("source.txt", {p.name for p in (root / "retrieved/blind-workspaces/translator").rglob("*")})
            self.assertFalse((root / "retrieved/role-spec/judge/formal-context.json").exists())

    def test_protected_support_and_role_budgets(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            engine = self.engine(root)
            support = root / "inputs/support/Research"
            support.mkdir()
            (support / "Model.lean").write_text("original definition")
            self.assertEqual(protected_sources(engine, root / "retrieved/workspace"), ["Research/Model.lean"])
            engine.config["revision"]["seconds"]["judge"] = 0
            with self.assertRaisesRegex(ValueError, "role budget"):
                validate_settings(engine.config)

    def test_only_retrieved_production_role_gets_memory(self):
        with TemporaryDirectory() as folder:
            root=Path(folder)
            engine=self.engine(root)
            def process(command,**kwargs):
                out=root/"retrieved/roles/planner"
                (out/"metrics.json").write_text('{"exit_code":0,"timed_out":false}')
                (out/"retrieval.json").write_text(json.dumps({"search_queries":[],"opened_artifacts":[],"decisions_influenced":[]}))
                self.assertIn("target=/memory,readonly"," ".join(command))
                self.assertIn("MEMORY_MODE=retrieved",command)
                self.assertIn("target=/workspace,readonly"," ".join(command))
                return SimpleNamespace(returncode=0)
            with patch("roles.subprocess.run",side_effect=process):
                launch(engine,"retrieved","planner","plan")

    def test_handoffs_reject_omitted_or_duplicate_targets(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            for targets in ([], ["T", "T"]):
                (root / "statement.json").write_text(json.dumps({"schema_version":1,"targets":targets,"construction_names":[]}))
                with self.assertRaises(ValueError): handoff(root, "formalizer")


if __name__ == "__main__":
    unittest.main()
