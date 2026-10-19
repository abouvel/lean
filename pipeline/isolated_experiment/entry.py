"""Fresh CLI actor; no prior conversation or host configuration is loaded."""
import json
import os
from pathlib import Path
import subprocess
import time

kind = os.environ.get("RUN_KIND", "builder")
condition = os.environ.get("MEMORY_MODE", "stateless")
out = Path("/output")
out.mkdir(exist_ok=True)
Path(os.environ["CODEX_HOME"]).mkdir(parents=True, exist_ok=True)
auth_link = Path(os.environ["CODEX_HOME"]) / "auth.json"
if not auth_link.exists():
    auth_link.symlink_to("/auth/auth.json")
started = time.time()
prompt = Path("/spec/REVIEWER.txt" if kind == "reviewer" else "/spec/PROMPT.txt").read_text()
if kind == "builder" and condition == "retrieved":
    prompt += "\nA read-only research-memory snapshot is available at /memory. Read its index, select relevant entries, and record every opened artifact ID and the concrete decision it influenced in /output/retrieval.md.\n"
command = ["codex", "exec", "--ignore-user-config", "--ignore-rules", "--ephemeral",
           "--skip-git-repo-check", "--json", "--color", "never",
           "--dangerously-bypass-approvals-and-sandbox",
           "-m", os.environ["EXPERIMENT_MODEL"],
           "-c", 'model_reasoning_effort="' + os.environ["REASONING_EFFORT"] + '"',
           "-c", 'web_search="disabled"', "-C", "/workspace",
           "-o", "/output/final.md", "-"]
limit = int(os.environ.get("TIME_LIMIT_SECONDS", "1200"))
meta = {"condition": condition, "kind": kind, "model": os.environ["EXPERIMENT_MODEL"],
        "reasoning_effort": os.environ["REASONING_EFFORT"], "started_unix": started,
        "time_limit_seconds": limit, "api_cost": "unknown", "aristotle_calls": 0}
(out / "actual-prompt.txt").write_text(prompt)
with (out / "events.jsonl").open("w") as stdout, (out / "stderr.log").open("w") as stderr:
    process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=stdout, stderr=stderr, text=True)
    try:
        process.communicate(prompt, timeout=limit)
        meta.update(exit_code=process.returncode, timed_out=False)
    except subprocess.TimeoutExpired:
        process.terminate()
        try:
            process.wait(timeout=15)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()
        meta.update(exit_code=process.returncode, timed_out=True)
meta["wall_time_seconds"] = round(time.time() - started, 3)
usage = None
compiler_commands = 0
for line in (out / "events.jsonl").read_text().splitlines():
    try:
        event = json.loads(line)
    except json.JSONDecodeError:
        continue
    if event.get("type") == "turn.completed":
        usage = event.get("usage")
    item = event.get("item", {})
    if event.get("type") == "item.completed" and item.get("type") == "command_execution":
        cmd = item.get("command", "")
        if "lake build" in cmd or "lake env lean" in cmd or "lean " in cmd:
            compiler_commands += 1
meta["token_usage"] = usage if usage is not None else "unknown"
meta["compiler_command_events"] = compiler_commands
meta["compiler_attempts_note"] = "Command events mentioning Lean/build, not individual lemma attempts."
(out / "metrics.json").write_text(json.dumps(meta, indent=2) + "\n")
print(json.dumps(meta), flush=True)
