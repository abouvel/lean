import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from metrics import apply_expert_labels, summarize_job


class ScorecardTests(unittest.TestCase):
    def test_disagreement_remains_visible_and_tokens_are_not_double_counted(self):
        role = {"model": "test", "reasoning_effort": "medium", "wall_time_seconds": 2,
                "token_usage": {"input_tokens": 10, "cached_input_tokens": 4, "output_tokens": 3}}
        result = {"job_id": "example", "condition": "stateless", "outcome": "needs_human", "success": False,
                  "record": {"passes": [{"roles": {"judge": role}, "critic": role,
                                         "builder": role, "direct_report": {"overall_verdict": "fail"},
                                         "roundtrip": {"overall_verdict": "pass"},
                                         "verification": {"formal_gate_passed": True,
                                                          "formal_audit": {"candidate_hash": "candidate"}}}]}}
        job = summarize_job(result, Path("."))
        self.assertTrue(job["reviewer_disagreement"])
        self.assertEqual(job["total_tokens"]["input_tokens"], 20)
        self.assertEqual(job["total_tokens"]["cached_input_tokens"], 8)
        self.assertEqual(job["total_tokens"]["reasoning_output_tokens"], "unknown")
        self.assertIsNone(job["expert_confirmed_success"])
        with self.assertRaises(ValueError):
            apply_expert_labels({"jobs": [job]}, {"example": {"candidate_hash": "wrong", "verdict": "fail"}})
        labeled = apply_expert_labels({"jobs": [job]}, {"example": {"candidate_hash": "candidate", "verdict": "fail"}})
        self.assertEqual(labeled["expert_comparison"]["roundtrip"]["false_passes"], 1)
        self.assertEqual(labeled["expert_comparison"]["direct_critic"]["agreements"], 1)

    def test_startup_timeout_is_not_a_formal_rejection_or_zero_usage(self):
        job = summarize_job({"job_id": "example", "condition": "retrieved",
                             "outcome": "infrastructure_error", "success": False,
                             "error": "Lean startup timed out"}, Path("."))
        self.assertTrue(job["timed_out"])
        self.assertEqual(job["lean_verification"], "not_run")
        self.assertEqual(job["total_tokens"]["input_tokens"], "unknown")
        self.assertEqual(job["roundtrip"], "not_run")
