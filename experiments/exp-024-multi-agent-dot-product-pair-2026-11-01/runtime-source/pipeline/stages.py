"""One sequential proof pass, composed from independently callable stages."""
import json
from contextlib import nullcontext

from critic import completed_review, read_retrieval_log, review


def read(path):
    return json.loads(path.read_text())


def build(engine, condition):
    if engine.config.get("revision"):
        from roles import produce
        return produce(engine, condition)
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
    revised = bool(getattr(engine, "config", {}).get("revision"))
    if revised:
        engine.stage_gate = gate
        from formal_context import FormalizationFailure
        try:
            builder = build(engine, condition)
        except FormalizationFailure as error:
            from engine import save
            from roles import aggregate, PRODUCTION
            invoked = {}
            for role in PRODUCTION:
                path = engine.directory / condition / "roles" / role / "metrics.json"
                if path.exists():
                    invoked[role] = read(path)
            builder = aggregate(invoked) if invoked else {}
            verification = {"formal_gate_passed": False, "build_and_scans_exit_code": 1,
                            "stage": "formalizer", "diagnostic": str(error)}
            save(engine.directory / condition / "evaluation/verification.log", str(error))
            save(engine.directory / condition / "evaluation/verification.json", verification)
            return {"status": "formal_failed", "builder": builder, "verification": verification,
                    "critic": {}, "roles": invoked}
    else:
        with gate("builder"):
            builder = build(engine, condition)
    with gate("verification"):
        verification = verify(engine, condition)
        if revised and verification["formal_gate_passed"]:
            from formal_context import extract, protected_declarations
            context, audit = extract(engine, condition, "final", evaluation=True)
            before = read(engine.directory / condition / "formal-audit/formalizer/context.json")
            audit["changed_declarations"] = protected_declarations(before, context)
            audit["passed"] = audit["passed"] and not audit["changed_declarations"]
            verification["formal_audit"] = audit
            verification["formal_gate_passed"] = audit["passed"]
            from engine import save
            save(engine.directory / condition / "evaluation/verification.json", verification)
            if not audit["passed"]:
                log = engine.directory / condition / "evaluation/verification.log"
                log.write_text(log.read_text() + "\nTrusted formal audit failed: " + json.dumps(audit) + "\n")
    result = {"builder": builder, "verification": verification, "critic": {}, "status": "formal_failed"}
    if not verification["formal_gate_passed"]:
        return result
    with gate("critic"):
        metrics, report = critique(engine, condition)
    if revised:
        from formal_context import translation_bundle, source_hashes
        from roundtrip import evaluate, route
        bundle = translation_bundle(context, builder["statement"])
        rt, evaluator_metrics = evaluate(engine, condition, bundle)
        if source_hashes(engine.directory / condition / "evaluation-workspace") != context["sources"]:
            raise RuntimeError("Candidate changed after semantic evaluation")
        status, decision = route(report, rt)
        result.update(critic=metrics, report=decision, status=status,
            direct_report=report, roundtrip=rt, roles={**builder["roles"], **evaluator_metrics})
        return result
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
