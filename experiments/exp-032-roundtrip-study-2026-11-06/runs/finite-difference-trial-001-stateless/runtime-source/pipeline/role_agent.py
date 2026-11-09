"""One fresh role session inside an isolated container; no host orchestration."""
import os
from pathlib import Path
from agent import run_agent, export_permissions

if __name__ == "__main__":
    role = os.environ["RESEARCH_ROLE"]
    run_agent(Path("/spec/ROLE.txt").read_text(), kind=role)
    if role in ("formalizer", "prover"):
        export_permissions(Path("/workspace/Research"))
