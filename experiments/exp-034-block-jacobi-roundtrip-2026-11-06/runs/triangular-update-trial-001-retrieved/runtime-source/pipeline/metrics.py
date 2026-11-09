"""Export measured job outcomes and compare reviewer verdicts with expert labels."""
import argparse
import json
from pathlib import Path

TOKEN_FIELDS = ("input_tokens", "cached_input_tokens", "output_tokens", "reasoning_output_tokens")
VERDICTS = {"pass", "fail", "uncertain"}


def sum_measured(values):
    return sum(values) if all(type(value) in (int, float) for value in values) else "unknown"


def verdict(report):
    value = report.get("overall_verdict")
    return value if value in VERDICTS else "not_run"


def usage(records):
    models = {(entry.get("model", "unknown"), entry.get("reasoning_effort", "unknown")) for entry in records}
    return {
        "sessions_with_metrics": len(records),
        "model_settings": [{"model": model, "reasoning_effort": effort} for model, effort in sorted(models)],
        "wall_seconds": sum_measured([entry.get("wall_time_seconds") for entry in records]),
        "tokens": {
            key: sum_measured([entry["token_usage"].get(key) if isinstance(entry.get("token_usage"), dict) else None
                               for entry in records])
            for key in TOKEN_FIELDS
        },
    }


def timed_out(result, passes, roles):
    errors = [result.get("error", ""), *(item.get("error", "") for item in passes)]
    if any(entry.get("timed_out") is True for entries in roles.values() for entry in entries):
        return True
    if any(item.get("verification", {}).get("build_and_scans_exit_code") == 124 for item in passes):
        return True
    errors = [message.lower() for message in errors if message]
    if any("timeout" in message or ("timed out" in message and "failed or timed out" not in message)
           for message in errors):
        return True
    return None if result["outcome"] == "infrastructure_error" else False


def summarize_job(result, job_root, elapsed="unknown"):
    record = result.get("record", {})
    passes = record.get("passes", [])
    last = passes[-1] if passes else {}
    metrics = record.get("metrics", {})
    roundtrip = last.get("roundtrip", {})
    direct = last.get("direct_report", last.get("report", {}) if not roundtrip else {})
    verification = last.get("verification", {})
    formal = verification.get("formal_gate_passed")
    roles = {}
    for item in passes:
        role_records = dict(item.get("roles", {}))
        if item.get("builder") and not role_records:
            role_records["builder"] = item["builder"]
        if item.get("critic"):
            role_records["direct_critic"] = item["critic"]
        for role, entry in role_records.items():
            roles.setdefault(role, []).append(entry)

    decisions = []
    for item in passes:
        evidence = item.get("retrieval_record")
        if not evidence or evidence == "unknown":
            continue
        root = job_root.resolve()
        path = (root / evidence).resolve()
        if path.is_relative_to(root) and path.suffix == ".json" and path.is_file():
            log = json.loads(path.read_text())
            decisions.extend({"pass": item["number"], **value}
                             for value in log.get("decisions_influenced", []))

    role_usage = {name: usage(entries) for name, entries in sorted(roles.items())}
    token_totals = {
        key: sum_measured([entry["tokens"][key] for entry in role_usage.values()])
        if role_usage and result["outcome"] != "infrastructure_error" else "unknown"
        for key in TOKEN_FIELDS
    }
    return {
        "job_id": result["job_id"],
        "task_id": record.get("task_id", "unknown"),
        "condition": result["condition"],
        "outcome": result["outcome"],
        "automated_success": result["success"],
        "lean_verification": "pass" if formal is True else "fail" if formal is False else "not_run",
        "direct_critic": verdict(direct),
        "roundtrip": verdict(roundtrip),
        "reviewer_disagreement": (verdict(direct) != verdict(roundtrip)) if direct and roundtrip else None,
        "roundtrip_requirements": roundtrip.get("requirements", []),
        "roundtrip_relation": roundtrip.get("relation"),
        "delivery_complete": roundtrip.get("delivery_complete"),
        "construction_complete": roundtrip.get("construction_complete"),
        "candidate_hash": verification.get("formal_audit", {}).get("candidate_hash"),
        "first_success_pass": metrics.get("first_success_pass"),
        "attempts": len(passes),
        "repair_attempts": max(0, len(passes) - 1),
        "timed_out": timed_out(result, passes, roles),
        "job_elapsed_seconds": elapsed,
        "proof_loop_seconds": metrics.get("wall_time_seconds", "unknown"),
        "roles": role_usage,
        "total_tokens": token_totals,
        "artifacts_opened": record.get("retrieved_artifacts", "unknown"),
        "reported_artifact_decisions": decisions,
        "expert_verdict": "pending",
        "expert_confirmed_success": None,
    }


def apply_expert_labels(scorecard, labels):
    """Compare independent, candidate-bound labels without changing model decisions."""
    by_id = {job["job_id"]: job for job in scorecard["jobs"]}
    for job_id, label in labels.items():
        job = by_id.get(job_id)
        if (job is None or not job["candidate_hash"] or label.get("candidate_hash") != job["candidate_hash"]
                or label.get("verdict") not in VERDICTS):
            raise ValueError("Expert verdict does not identify a reviewed candidate: " + job_id)
        job["expert_verdict"] = label["verdict"]
        if label["verdict"] in {"pass", "fail"}:
            job["expert_confirmed_success"] = label["verdict"] == "pass" and job["lean_verification"] == "pass"
    accuracy = {}
    for name in ("roundtrip", "direct_critic"):
        reviewed = [job for job in by_id.values() if job["expert_verdict"] in {"pass", "fail"}]
        accuracy[name] = {
            "expert_decisive_cases": len(reviewed),
            "agreements": sum(job[name] == job["expert_verdict"] for job in reviewed),
            "false_passes": sum(job[name] == "pass" and job["expert_verdict"] == "fail" for job in reviewed),
            "false_rejections": sum(job[name] == "fail" and job["expert_verdict"] == "pass" for job in reviewed),
            "uncertain": sum(job[name] == "uncertain" for job in reviewed),
            "not_run": sum(job[name] == "not_run" for job in reviewed),
        }
    scorecard["expert_comparison"] = accuracy
    return scorecard


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("batch", type=Path)
    parser.add_argument("--expert-labels", type=Path, required=True)
    args = parser.parse_args()
    data = json.loads((args.batch / "scorecard.json").read_text())
    labels = json.loads(args.expert_labels.read_text())
    print(json.dumps(apply_expert_labels(data, labels), indent=2))


if __name__ == "__main__":
    main()
