"""Deterministic run records, not agent-written claims of learned knowledge."""
import json
from pathlib import Path
from engine import save


def validate(record):
    for key in ("schema_version", "artifact_id", "experiment_id", "condition", "status", "success",
                "task_id", "model", "reasoning_effort", "starting_commit", "artifact_snapshot",
                "retrieved_artifacts", "verification_command", "passes", "metrics", "reuse"):
        if key not in record:
            raise ValueError(f"Missing artifact field: {key}")
    if record["schema_version"] != 1 or record["condition"] not in ("stateless", "retrieved"):
        raise ValueError("Unsupported artifact version/condition")
    if type(record["success"]) is not bool or not isinstance(record["passes"], list):
        raise ValueError("Invalid artifact outcome")
    if record["success"] and (not record["passes"] or record["passes"][-1]["status"] != "accepted"):
        raise ValueError("Success requires an accepted pass")
    if record["reuse"].get("approved") is not False:
        raise ValueError("Generated artifacts cannot automatically approve their own reuse")


def write(directory, record):
    validate(record)
    stem = record["artifact_id"]
    save(directory / "artifacts" / (stem + ".json"), record)
    # Keep the repository's required human-readable run summary, linking to JSON.
    fields = ("artifact_id", "experiment_id", "condition", "task_id", "model", "reasoning_effort",
              "starting_commit", "artifact_snapshot", "retrieved_artifacts", "verification_command", "success")
    text = "# Bounded agent run\n\n```text\n" + "\n".join(f"{key}: {record[key]}" for key in fields)
    text += f"\nstatus: {'verified' if record['success'] else 'partial'}\nmemory_mode: {record['condition']}\n```\n\n"
    sections = {
        "Request": "Compare equal fixed pass budgets, with and without frozen artifacts.",
        "Target": record["task_id"], "Result": record["outcome"],
        "Decisions and reasoning": "Only verifier/critic evidence authorizes acceptance. Uncertain or invalid reviews stop for attention.",
        "What worked": "See pass-level evidence; no benefit inferred automatically.",
        "What failed": "See recorded failed gates and diagnostics; infrastructure failures are separate.",
        "Reusable observations": "Not promoted. Any candidate lesson needs review and answer-leakage checks.",
        "Evidence": f"[Structured run record]({stem}.json)",
        "Remaining limitations": "External-memory reuse only; no weight learning or causal conclusion. Human semantic sign-off not claimed.",
        "Metrics": "Unknown measurements remain unknown; see the JSON record."}
    for heading, body in sections.items():
        text += f"## {heading}\n\n{body}\n\n"
    save(directory / "artifacts" / (stem + ".md"), text)
    index = directory / "artifacts/index.md"
    previous = index.read_text() if index.exists() else "# Run artifacts\n"
    save(index, f"- [{stem}]({stem}.md): {record['status']}; {record['condition']}\n\n" + previous)
