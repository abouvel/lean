"""Deterministically score preserved LLM critic reports against hidden labels."""
import argparse
import json
from pathlib import Path

from critic import load_catalog, read_review


def load(path):
    return json.loads(Path(path).read_text())


def score(manifest_path):
    """Score reports without exposing expected labels to the critic session."""
    manifest_path = Path(manifest_path)
    root = manifest_path.parent
    manifest = load(manifest_path)
    if not isinstance(manifest, dict) or manifest.get("schema_version") != 1:
        raise ValueError("Invalid critic benchmark manifest")
    catalog_path = root / manifest["catalog"]
    catalog = load_catalog(catalog_path)
    allowed_defects = {item["id"] for item in catalog["defect_categories"]}
    cases = manifest.get("cases")
    if not isinstance(cases, list) or not cases:
        raise ValueError("Critic benchmark needs at least one case")
    ids = [case.get("id") for case in cases]
    if any(not isinstance(case_id, str) or not case_id for case_id in ids) or len(ids) != len(set(ids)):
        raise ValueError("Critic benchmark case ids must be unique strings")

    rows = []
    for case in cases:
        expected = case.get("expected_verdict")
        expected_defects = case.get("expected_defects")
        if expected not in ("pass", "fail", "uncertain"):
            raise ValueError(f"Invalid expected verdict for {case['id']}")
        if not isinstance(expected_defects, list) or not set(expected_defects) <= allowed_defects:
            raise ValueError(f"Invalid expected defects for {case['id']}")
        row = {"id": case["id"], "expected_verdict": expected,
               "expected_defects": expected_defects, "status": "scored"}
        metrics_path = root / case["metrics"] if case.get("metrics") else None
        if metrics_path and metrics_path.exists() and load(metrics_path).get("timed_out"):
            row.update(status="timeout", predicted_verdict="unavailable", predicted_defects=[])
            rows.append(row)
            continue
        report_path = root / case["report"]
        try:
            report = read_review(report_path.parent, report_path.name, catalog=catalog)
        except (OSError, ValueError, json.JSONDecodeError) as error:
            row.update(status="invalid_report", predicted_verdict="unavailable",
                       predicted_defects=[], error=str(error))
            rows.append(row)
            continue
        predicted_defects = sorted({defect for item in report["requirements"]
                                    for defect in item["defect_categories"]})
        row.update(predicted_verdict=report["overall_verdict"],
                   predicted_defects=predicted_defects,
                   verdict_correct=report["overall_verdict"] == expected,
                   expected_defects_found=set(expected_defects) <= set(predicted_defects),
                   false_pass=expected != "pass" and report["overall_verdict"] == "pass",
                   false_rejection=expected == "pass" and report["overall_verdict"] == "fail")
        rows.append(row)

    scored = [row for row in rows if row["status"] == "scored"]
    expected_defect_count = sum(len(row["expected_defects"]) for row in scored)
    found_defect_count = sum(len(set(row["expected_defects"]) & set(row["predicted_defects"])) for row in scored)
    return {
        "schema_version": 1,
        "cases": rows,
        "summary": {
            "total_cases": len(rows),
            "scored_cases": len(scored),
            "verdicts_correct": sum(row["verdict_correct"] for row in scored),
            "false_passes": sum(row["false_pass"] for row in scored),
            "false_rejections": sum(row["false_rejection"] for row in scored),
            "invalid_reports": sum(row["status"] == "invalid_report" for row in rows),
            "timeouts": sum(row["status"] == "timeout" for row in rows),
            "expected_defects_found": found_defect_count,
            "expected_defects_total": expected_defect_count
        }
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = score(args.manifest)
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
