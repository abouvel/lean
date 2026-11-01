"""Resume the frozen run after an infrastructure-only cache ownership failure."""
import json
import os
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import run_benchmark as benchmark

benchmark.check_frozen()
config = json.loads((HERE / "experiment.json").read_text())
protocol = json.loads((HERE / "protocol.json").read_text())
engine = benchmark.Engine(
    HERE,
    config,
    Path.home() / ".elan/toolchains/leanprover--lean4---v4.28.0",
    benchmark.ROOT / ".lake/packages",
    Path(os.environ.get("RESEARCH_CODEX_AUTH", "/mnt/c/Users/austi/.codex/auth.json")),
    benchmark.check_frozen,
)
benchmark.verify_cases(config, engine)
benchmark.write_benchmark_manifest(protocol)
try:
    benchmark.review(engine)
finally:
    engine.cleanup()
result = benchmark.score(HERE / "benchmark.json")
benchmark.save(HERE / "scores.json", result)
print(json.dumps(result["summary"], indent=2))
