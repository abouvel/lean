"""Create the preregistered critic cases without calling a model."""
import json
from pathlib import Path
import shutil


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
COMPLETE = ROOT / "experiments/exp-001-binary-tree/stateless/workspace/Research/Submission.lean"
INCOMPLETE = ROOT / "experiments/exp-004-critic-240s-2026-10-23/stateless/passes/pass-002/stateless/workspace/Research/Submission.lean"
PROPOSITION_ONLY = ROOT / "experiments/exp-002-bounded-2026-10-23/stateless/workspace/Research/Submission.lean"
CONFIG_SOURCE = ROOT / "experiments/exp-005-critic-canary-2026-10-27/canary-complete/evaluation-workspace"
INPUT_SOURCE = ROOT / "experiments/exp-005-critic-canary-2026-10-27/inputs"
RUBRIC_SOURCE = ROOT / "experiments/exp-005-critic-canary-2026-10-27/evaluator/REVIEWER.txt"
CATALOG_SOURCE = ROOT / "pipeline/examples/critic-requirements.json"
CASES = ("known-complete", "missing-original-input-link", "proposition-only",
         "concrete-example-only", "conclusion-assumed")


def variant_sources():
    complete = COMPLETE.read_text()
    marker = "/-- Theorem 3.1, in an occurrence-preserving list formulation."
    prefix = complete.split(marker, 1)[0]
    concrete = prefix + r'''
/-- A fixed execution trace is not the universally quantified backward-error theorem. -/
theorem concrete_example_only :
    stagesValues (fun x y : ℝ => x + y) (depth 5) [2, 3, 4, 5, 6] = [20] := by
  norm_num [depth, stagesValues, roundValues, pairValues]

end Bhola
'''
    assumed = prefix + r'''
/-- This has the requested conclusion only because that conclusion is assumed. -/
theorem theorem_3_1 (add : ℝ → ℝ → ℝ) (xs : List ℝ)
    (hn : xs ≠ []) {u : ℝ} (hu : 0 ≤ u) (hm : ExecutionModel add u xs)
    (hd : (depth xs.length : ℝ) * u < 1)
    (conclusion : ∃ Δ : Fin xs.length → ℝ,
      algorithm add xs = ∑ i : Fin xs.length, (xs.get i + Δ i) ∧
      ∀ i, |Δ i| ≤ gamma (depth xs.length) u * |xs.get i|) :
    ∃ Δ : Fin xs.length → ℝ,
      algorithm add xs = ∑ i : Fin xs.length, (xs.get i + Δ i) ∧
      ∀ i, |Δ i| ≤ gamma (depth xs.length) u * |xs.get i| := by
  exact conclusion

end Bhola
'''
    return {
        "known-complete": complete,
        "missing-original-input-link": INCOMPLETE.read_text(),
        "proposition-only": PROPOSITION_ONLY.read_text(),
        "concrete-example-only": concrete,
        "conclusion-assumed": assumed
    }


def main():
    protocol = json.loads((HERE / "protocol.json").read_text())
    if tuple(item["id"] for item in protocol["cases"]) != CASES:
        raise RuntimeError("Protocol cases and generator cases differ")
    inputs = HERE / "inputs"
    evaluator = HERE / "evaluator"
    memory = HERE / "memory"
    for directory in (inputs, evaluator, memory):
        directory.mkdir(exist_ok=False)
    for name in ("source.txt", "source.pdf"):
        shutil.copyfile(INPUT_SOURCE / name, inputs / name)
    shutil.copyfile(RUBRIC_SOURCE, evaluator / "REVIEWER.txt")
    shutil.copyfile(CATALOG_SOURCE, evaluator / "requirements.json")
    (memory / "index.md").write_text("# Empty memory\n")
    sources = variant_sources()
    for case in CASES:
        workspace = HERE / case / "evaluation-workspace"
        (workspace / "Research").mkdir(parents=True)
        (workspace / ".lake").mkdir()
        for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
            shutil.copyfile(CONFIG_SOURCE / name, workspace / name)
        (workspace / "Research.lean").write_text("import Research.Submission\n")
        (workspace / "Research/Submission.lean").write_text(sources[case])
        (HERE / case / "evaluation").mkdir()
    config = {
        "name": HERE.name,
        "task_id": protocol["task_id"],
        "model": protocol["model"],
        "reasoning_effort": protocol["reasoning_effort"],
        "conditions": list(CASES),
        "builder_seconds": 1,
        "critic_seconds": protocol["critic_time_limit_seconds"],
        "image": "research-proof-pilot-ready:2026-10-19",
        "inputs": "inputs",
        "memory": "memory",
        "evaluator": "evaluator",
        "aristotle_enabled": False,
        "resources": {"memory": "8g", "cpus": 2, "pids": 256},
        "verification_command": protocol["verification_command"]
    }
    (HERE / "experiment.json").write_text(json.dumps(config, indent=2) + "\n")


if __name__ == "__main__":
    main()
