"""Preregister a fresh dot-product builder task; exclude its completed proof."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = ROOT / "experiments/exp-001-binary-tree"
TARGET = ROOT / "experiments/exp-011-dot-product-critic-2026-10-28"
SUPPORT = (
    "Common/FloatingPoint/Model.lean",
    "Common/FloatingPoint/Gamma.lean",
    "Projects/BinaryTreeReduction/Tree.lean",
    "Projects/BinaryTreeReduction/Algorithm.lean",
    "Projects/BinaryTreeReduction/Reduction.lean",
)

PROMPT = '''Build the floating-point dot-product proof described in /spec/source.txt.

The five approved supporting Lean modules are under /spec/support/Research.
Copy them, retaining their relative paths, into /workspace/Research. They supply
the abstract relative-error Model, gamma bounds, Tree, rounded sum, and
supporting reduction results. Read them as mathematical prerequisites. Do not
modify these supplied definitions or lemmas. The dot-product implementation and
target proof have not been supplied: define the exact and rounded product trees,
define roundedDotProduct as rounded multiplication followed by rounded tree
addition, and prove the full componentwise backward-error theorem.

Put the new definitions, supporting lemmas, and final theorem in
/workspace/Research/Submission.lean. Import the supplied reduction module there.
No locked theorem statement is supplied; choose an appropriate formal statement
matching the original task. Keep the theorem statement distinct from its proof.
The final result must be relative to exactProductTree with gamma(depth+1,u),
quantified over every Model and pair tree under only the specified smallness
assumption. Declaration names other than the mathematical objects may vary.

Use local Lean compilation and small lemmas. Do not use proof placeholders,
custom axioms, changed protected configuration, or Aristotle. The protected
/workspace/Research.lean imports Research.Submission. The formal verifier will
compile all submitted Lean modules and scan them for placeholders/custom axioms;
the independent critic will check semantics and original assumptions.
'''


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value if isinstance(value, str) else json.dumps(value, indent=2) + "\n")


def main():
    if (HERE / "frozen-manifest.json").exists():
        raise RuntimeError("Task already frozen")
    config = {
        "name": HERE.name, "task_id": "floating-point-dot-product-backward-error",
        "model": "gpt-6.1-sol", "reasoning_effort": "medium",
        "conditions": ["stateless", "retrieved"], "max_passes": 2,
        "builder_seconds": 180, "critic_seconds": 240,
        "image": "research-proof-pilot-ready:2026-10-19",
        "inputs": "inputs", "memory": "memory", "evaluator": "evaluator",
        "aristotle_enabled": False,
        "resources": {"memory": "8g", "cpus": 2, "pids": 256},
    }
    save(HERE / "experiment.json", config)
    for folder in ("inputs", "memory", "evaluator"):
        (HERE / folder).mkdir(exist_ok=False)
    shutil.copyfile(TARGET / "inputs/source.txt", HERE / "inputs/source.txt")
    shutil.copyfile(TARGET / "inputs/source.pdf", HERE / "inputs/source.pdf")
    save(HERE / "inputs/PROMPT.txt", PROMPT)
    for relative in SUPPORT:
        dest = HERE / "inputs/support/Research" / relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / "lean/Research" / relative, dest)
    for name in ("index.md", "general-lean.md"):
        shutil.copyfile(BASE / "memory" / name, HERE / "memory" / name)
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "Research.lean"):
        shutil.copyfile(BASE / "evaluator" / name, HERE / "evaluator" / name)
    shutil.copyfile(ROOT / "pipeline/verify.sh", HERE / "evaluator/verify.sh")
    for name in ("REVIEWER.txt", "requirements.json"):
        shutil.copyfile(TARGET / "evaluator" / name, HERE / "evaluator" / name)
    protocol = {
        "experiment_id": HERE.name, "task_id": config["task_id"],
        "purpose": "Live end-to-end test of the modular proof-building pipeline on one dot-product theorem, one stateless/retrieved pair.",
        "model": config["model"], "reasoning_effort": config["reasoning_effort"],
        "allowed_tools": ["local Lean and Mathlib", "approved supporting source modules", "frozen generic memory only for retrieved builder"],
        "time_limit": {"max_passes": 2, "builder_seconds_per_pass": 180, "critic_seconds_per_pass": 240, "job_seconds": 2400},
        "verification_command": "bash pipeline/verify.sh",
        "acceptance_tests": [
            "Both jobs finish with valid collected result bundles and no infrastructure error.",
            "Each accepted proof passes the full Lean build and placeholder/custom-axiom scans.",
            "Each accepted proof receives a valid independent critic pass covering the complete original target.",
            "The completed dot-product proof and all prior dot-product reports/candidates are absent from builder inputs and the retrieval snapshot.",
            "Compare success before passes, time and tokens; retain failures and unavailable measurements as unknown."
        ],
        "snapshot_review": "Only five prerequisite modules are supplied to both builders; DotProduct.lean is excluded. Generic memory includes pilot-general-lean-001 only. No prior candidates, verdicts, reports, or transcripts are exposed.",
    }
    save(HERE / "protocol.json", protocol)
    save(HERE / "batch.json", {
        "schema_version": 1,
        "limits": {"jobs": 1, "model_calls": 1, "lean_builds": 1, "ram_gib": 12, "job_seconds": 2400},
        "tasks": [{"id": "dot-product", "config": str((HERE / "experiment.json").relative_to(ROOT)),
                   "trials": 1, "memory_review": {"target_answer_excluded": True,
                   "note": "Reviewed pilot-general-lean-001: generic tactic, denominator, and stale-module notes only. Completed dot-product proof, previous benchmark candidates, verdicts, and reports are excluded from all builder inputs."}}],
    })
    files = [path for path in HERE.rglob("*") if path.is_file()]
    commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], check=True, capture_output=True, text=True).stdout.strip()
    save(HERE / "frozen-manifest.json", {"experiment_id": HERE.name,
        "starting_commit": commit, "mode": "preregistered-proof-task-template",
        "hashes": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in files}})


if __name__ == "__main__":
    main()
