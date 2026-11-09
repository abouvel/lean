"""Exercise host writes to real UID-1100 trusted-verifier exports, no model call."""
import json
from pathlib import Path
import shutil
import subprocess
import sys

root=Path(__file__).resolve().parent
out=root/"output"
work=root/"workspace"
out.mkdir()
out.chmod(0o777)
(work/"Research").mkdir(parents=True)
(work/"Research/Submission.lean").write_text("import Mathlib\n-- canary\n-- no proof claim\n")
(root/"verify.sh").write_text("#!/bin/sh\nexit 0\n")
shutil.copyfile(sys.argv[1],root/"verify.py")
subprocess.run(["docker","run","--rm","--read-only","--network","none","--cap-drop=ALL",
    "--mount",f"type=bind,source={work},target=/workspace,readonly",
    "--mount",f"type=bind,source={out},target=/output",
    "--mount",f"type=bind,source={root/'verify.sh'},target=/trusted/verify.sh,readonly",
    "--mount",f"type=bind,source={root/'verify.py'},target=/trusted/verify.py,readonly",
    "research-proof-pilot-ready:2026-10-19","python3","/trusted/verify.py"],check=True)
for name in ("verification.json","verification.log"):
    path=out/name
    assert path.stat().st_mode & 0o777 == 0o666
    path.write_text(path.read_text())
(root/"result.json").write_text(json.dumps({"passed":True,"model_calls":0,
    "scope":"Container-to-host output permissions only; shell verification is a stub"},indent=2)+"\n")
print("VERIFIER_EXPORT_CANARY_PASS")
