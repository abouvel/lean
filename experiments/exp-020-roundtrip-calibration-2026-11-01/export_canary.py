"""Exercise the real host/container ownership split without any model call."""
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
out=HERE/"export-permission-canary"
out.mkdir()
out.chmod(0o777)
code='''import sys, pathlib
sys.path.insert(0,"/runner")
from agent import export_permissions
p=pathlib.Path("/output/private.json")
p.write_text("{}")
p.chmod(0o600)
export_permissions(pathlib.Path("/output"))
print("EXPORT_CANARY_PASS")
'''
r=subprocess.run(["docker","run","--rm","--network","none",
    "--mount",f"type=bind,source={out},target=/output",
    "--mount",f"type=bind,source={ROOT/'pipeline/agent.py'},target=/runner/agent.py,readonly",
    "research-proof-pilot-ready:2026-10-19","python3","-c",code],capture_output=True,text=True)
print(r.stdout+r.stderr)
assert r.returncode==0
assert (out/"private.json").read_text()=="{}"
assert (out/"private.json").stat().st_mode & 0o777==0o666
print("HOST_CAN_READ_ACTOR_ATOMIC_FILE")
