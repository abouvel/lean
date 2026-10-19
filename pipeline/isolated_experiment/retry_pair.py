"""Separate paired experiment after model-capacity interruption; preserves originals."""
import argparse
import json
import sys

import run

run.RUN = run.REPO / "experiments/memory-ablation/2026-10-19-binary-tree-pilot-gpt61"
run.MODEL = "gpt-6.1-sol"
run.IMAGE = "research-proof-pilot-ready:2026-10-19"
run.NET = "research-proof-pilot61-internal"
run.PROXY = "research-proof-pilot61-proxy"


def network_ready():
    existing = run.call(["docker", "network", "inspect", run.NET], check=False)
    if existing.returncode:
        run.call(["docker", "network", "create", "--internal", run.NET])
    inspected = run.call(["docker", "inspect", run.PROXY], check=False)
    if not inspected.returncode:
        if json.loads(inspected.stdout)[0]["State"]["Running"]:
            return
        raise RuntimeError("A stopped proxy exists; inspect it before proceeding.")
    run.call(["docker", "run", "-d", "--name", run.PROXY, "--read-only", "--cap-drop=ALL",
              "--security-opt=no-new-privileges", "--pids-limit=64", "--memory=256m",
              "--network", "bridge", *run.mount(run.TOOLS / "proxy.py", "/base-proxy.py", True),
              *run.mount(run.TOOLS / "proxy_ready.py", "/proxy.py", True),
              run.IMAGE, "python3", "/proxy.py"])
    run.call(["docker", "network", "connect", "--alias", "model-proxy", run.NET, run.PROXY])


run.network = network_ready


def connectivity():
    run.check_frozen()
    network_ready()
    out = run.RUN / "connectivity"
    out.mkdir(exist_ok=True)
    run.ownership(out)
    command = run.container_args("stateless", output=out)
    command += run.mount(run.TOOLS / "smoke_model.py", "/runner/smoke_model.py", True)
    result = run.call([*command, run.IMAGE, "python3", "/runner/smoke_model.py"], check=False, timeout=110)
    print(result.stdout, result.stderr, flush=True)
    return result.returncode


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("phase", choices=["prepare", "preflight", "connectivity", "builders", "evaluate", "review", "summarize", "cleanup"])
    phase = parser.parse_args().phase
    if phase == "connectivity":
        sys.exit(connectivity())
    getattr(run, phase)()
