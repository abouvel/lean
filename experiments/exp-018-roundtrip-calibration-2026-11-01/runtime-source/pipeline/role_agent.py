"""One fresh role session inside an isolated container; no host orchestration."""
import os
from pathlib import Path
from agent import run_agent

if __name__ == "__main__":
    run_agent(Path("/spec/ROLE.txt").read_text(), kind=os.environ["RESEARCH_ROLE"])
