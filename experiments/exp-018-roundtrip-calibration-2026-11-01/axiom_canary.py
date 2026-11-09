"""A private axiom evades the legacy regex but must fail the elaborated audit."""
from pathlib import Path
import shutil
import sys
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0,str(ROOT/"pipeline"))
from engine import Engine
from formal_context import extract

case = HERE/"axiom-canary"
(case/"workspace/Research").mkdir(parents=True)
(case/"workspace/.lake/packages").mkdir(parents=True)
for name in ("lakefile.toml","lake-manifest.json","lean-toolchain","Research.lean"):
    shutil.copyfile(HERE/"known-complete/workspace"/name,case/"workspace"/name)
(case/"workspace/Research/Submission.lean").write_text(
    "namespace Research\nprivate axiom impossible : False\ntheorem target : False := impossible\nend Research\n")
config=json.loads((HERE/"experiment.json").read_text())
config["conditions"]=["axiom-canary"]
engine=Engine(HERE,config,Path.home()/".elan/toolchains/leanprover--lean4---v4.28.0",
    ROOT/".lake/packages",Path("/nonexistent-auth"),lambda:None)
engine.evaluate()
legacy=json.loads((case/"evaluation/verification.json").read_text())
assert legacy["formal_gate_passed"],legacy
context,audit=extract(engine,"axiom-canary","dependency-canary",evaluation=True)
assert not audit["passed"] and audit["unapproved_axioms"],audit
print(json.dumps({"legacy_gate_passed":True,"new_audit_rejected":True,
                 "unapproved_axioms":audit["unapproved_axioms"]},indent=2))
