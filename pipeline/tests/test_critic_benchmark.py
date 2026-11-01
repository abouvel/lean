"""Deterministic scoring tests for preserved LLM critic reports."""
import json
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
import unittest

PIPELINE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PIPELINE))
from critic_benchmark import score


class CriticBenchmarkTests(unittest.TestCase):
    def catalog(self):
        return {"schema_version": 1,
                "requirements": [{"id": "target-completeness", "description": "Prove target"}],
                "defect_categories": [{"id": "missing-final-theorem", "description": "No theorem"}]}

    def report(self, verdict, defects):
        return {"overall_verdict": verdict, "phase": "final", "target_evidence": "Submission.lean:10",
                "requirements": [{"requirement_id": "target-completeness", "requirement": "Prove target",
                                  "evidence": "Submission.lean:10", "verdict": verdict,
                                  "defect_categories": defects,
                                  "correction": "" if verdict == "pass" else "Prove it"}],
                "assumptions_added": [], "missing_obligations": [] if verdict == "pass" else ["target"],
                "limitations": []}

    def test_scores_semantics_contract_failures_and_timeouts_separately(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            (root / "requirements.json").write_text(json.dumps(self.catalog()))
            (root / "good.json").write_text(json.dumps(self.report("pass", [])))
            (root / "bad.json").write_text(json.dumps(self.report("fail", ["missing-final-theorem"])))
            (root / "invalid.json").write_text("{}")
            (root / "timeout.json").write_text('{"timed_out": true}')
            manifest = {"schema_version": 1, "catalog": "requirements.json", "cases": [
                {"id": "correct", "report": "good.json", "expected_verdict": "pass", "expected_defects": []},
                {"id": "missing", "report": "bad.json", "expected_verdict": "fail",
                 "expected_defects": ["missing-final-theorem"]},
                {"id": "invalid", "report": "invalid.json", "expected_verdict": "fail",
                 "expected_defects": ["missing-final-theorem"]},
                {"id": "timeout", "report": "absent.json", "metrics": "timeout.json",
                 "expected_verdict": "fail", "expected_defects": ["missing-final-theorem"]}]}
            (root / "benchmark.json").write_text(json.dumps(manifest))
            result = score(root / "benchmark.json")
            self.assertEqual(result["summary"], {
                "total_cases": 4, "scored_cases": 2, "verdicts_correct": 2,
                "false_passes": 0, "false_rejections": 0, "invalid_reports": 1,
                "timeouts": 1, "expected_defects_found": 1, "expected_defects_total": 1})

    def test_false_pass_is_counted_as_semantic_failure(self):
        with TemporaryDirectory() as folder:
            root = Path(folder)
            (root / "requirements.json").write_text(json.dumps(self.catalog()))
            (root / "report.json").write_text(json.dumps(self.report("pass", [])))
            (root / "benchmark.json").write_text(json.dumps({
                "schema_version": 1, "catalog": "requirements.json", "cases": [{
                    "id": "false-pass", "report": "report.json", "expected_verdict": "fail",
                    "expected_defects": ["missing-final-theorem"]}]}))
            result = score(root / "benchmark.json")
            self.assertEqual(result["summary"]["false_passes"], 1)
            self.assertEqual(result["summary"]["verdicts_correct"], 0)


if __name__ == "__main__":
    unittest.main()
