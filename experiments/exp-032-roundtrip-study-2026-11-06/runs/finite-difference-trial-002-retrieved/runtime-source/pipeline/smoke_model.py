"""Connectivity-only request in a disposable session, with no proof input."""
import os
from pathlib import Path
import subprocess

home = Path(os.environ["CODEX_HOME"])
home.mkdir(parents=True, exist_ok=True)
(home / "auth.json").symlink_to("/auth/auth.json")
command = ["codex", "exec", "--ignore-user-config", "--ignore-rules", "--ephemeral",
           "--skip-git-repo-check", "--json", "--color", "never", "-s", "read-only",
           "-m", os.environ["EXPERIMENT_MODEL"], "-c", 'model_reasoning_effort="medium"',
           "-c", 'web_search="disabled"', "Respond exactly READY. Do not use tools or read any files."]
result = subprocess.run(command, capture_output=True, text=True, timeout=90)
Path("/output/connectivity-events.jsonl").write_text(result.stdout)
Path("/output/connectivity-stderr.log").write_text(result.stderr)
print("CLI exit:", result.returncode)
print(result.stdout[-2000:])
print(result.stderr[-1000:])
raise SystemExit(result.returncode)
