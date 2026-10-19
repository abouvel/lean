"""Trusted evaluation, executed in a fresh offline container."""
import json
from pathlib import Path
import subprocess
import time

root, out = Path("/workspace"), Path("/output")
out.mkdir(exist_ok=True)
start = time.time()
try:
    process = subprocess.run(["bash", "/trusted/verify.sh"], cwd=root,
                             capture_output=True, text=True, timeout=240)
    code, log = process.returncode, process.stdout + process.stderr
except subprocess.TimeoutExpired as error:
    code, log = 124, "Verification timeout after 240 seconds.\n"
    if error.stdout:
        log += error.stdout.decode() if isinstance(error.stdout, bytes) else error.stdout
files = list((root / "Research").rglob("*.lean"))
nontrivial = any(len(p.read_text().splitlines()) > 2 for p in files)
result = {"verification_command": "bash pipeline/verify.sh", "build_and_scans_exit_code": code,
          "nontrivial_submission": nontrivial, "formal_gate_passed": code == 0 and nontrivial,
          "semantic_review": "pending", "wall_time_seconds": round(time.time() - start, 3),
          "source_files": [str(p.relative_to(root)) for p in files],
          "source_lines": sum(len(p.read_text().splitlines()) for p in files),
          "limitation": "Compilation alone does not establish the original theorem or algorithm. Semantic review is required."}
(out / "verification.log").write_text(log)
(out / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result), flush=True)
