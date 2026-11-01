"""One sequential proof pass, composed from independently callable stages."""
import json
from contextlib import nullcontext

from critic import completed_review, read_retrieval_log, review


def read(path):
    return json.loads(path.read_text())


def build(engine, condition):
    engine.builders()
    metrics = read(engine.directory / condition / "output/metrics.json")
    if metrics["exit_code"] != 0 and not metrics.get("timed_out"):
        raise RuntimeError("Builder service/process failed (not a theorem failure)")
    return metrics


def verify(engine, condition):
    engine.evaluate()
    result = read(engine.directory / condition / "evaluation/verification.json")
    if result.get("build_and_scans_exit_code") == 124:
        raise RuntimeError("Verification infrastructure timed out")
    if type(result.get("formal_gate_passed")) is not bool:
        raise ValueError("Verifier must report a boolean formal gate")
    return result


def critique(engine, condition):
    review(engine)
    output = engine.directory / condition / "review"
    metrics = read(output / "metrics.json")
    report = completed_review(output, metrics)
    if engine.config.get("critic_memory_enabled") and engine.memory_mode(condition) == "retrieved":
        read_retrieval_log(output)
    return metrics, report


def execute(engine, condition, *, gate=None):
    """A gate can reserve shared resources and publish stage/heartbeat state.

    Gates cover entire model stages because agents can invoke Lean themselves.
    Calling this function without a gate preserves the single-run workflow.
    """
    gate = gate or getattr(engine, "stage_gate", lambda stage: nullcontext())
    with gate("builder"):
        builder = build(engine, condition)
    with gate("verification"):
        verification = verify(engine, condition)
    result = {"builder": builder, "verification": verification, "critic": {}, "status": "formal_failed"}
    if not verification["formal_gate_passed"]:
        return result
    with gate("critic"):
        metrics, report = critique(engine, condition)
    result.update(critic=metrics, report=report,
                  status={"pass": "accepted", "fail": "critic_failed", "uncertain": "needs_human"}[report["overall_verdict"]])
    return result


def repair_feedback(directory, condition, result, number):
    """Only actionable corrections and formal diagnostics return to this job."""
    report = result.get("report", {})
    return {
        "schema_version": 1, "previous_pass": number,
        "formal_gate_passed": result["verification"]["formal_gate_passed"],
        "corrections": [{"requirement_id": item.get("requirement_id", "legacy"),
                         "requirement": item["requirement"], "correction": item["correction"]}
                        for item in report.get("requirements", []) if item["verdict"] != "pass"],
        "verification_log": (directory / condition / "evaluation/verification.log").read_text(),
    }
