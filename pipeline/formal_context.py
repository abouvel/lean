"""Trusted Lean elaboration, transitive axiom audit, and candidate fingerprints."""
import hashlib
import json
from pathlib import Path
import subprocess

from engine import TOOLS, mount, ownership, save

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


class FormalizationFailure(RuntimeError):
    """A candidate construction/skeleton failure that can receive bounded repair."""


def source_hashes(work):
    files = sorted((Path(work) / "Research").rglob("*.lean"))
    result = {}
    for path in files:
        if path.is_symlink() or any(p.is_symlink() for p in path.parents):
            raise ValueError("Candidate source symlink")
        result[str(path.relative_to(work))] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def fingerprint(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()).hexdigest()


def parse_extraction(stdout):
    prefix = "FORMAL_CONTEXT_JSON:"
    records = [line[len(prefix):] for line in stdout.splitlines() if line.startswith(prefix)]
    if len(records) != 1:
        raise ValueError("Expected exactly one trusted Lean context record")
    result = json.loads(records[0])
    if result.get("schema_version") != 1 or not isinstance(result.get("declarations"), list) or not result["declarations"]:
        raise ValueError("Empty or invalid elaborated context")
    if not isinstance(result.get("axioms"), list) or not all(isinstance(x, str) for x in result["axioms"]):
        raise ValueError("Invalid axiom dependencies")
    names = []
    for declaration in result["declarations"]:
        for key in ("name", "module", "kind", "type", "body"):
            if not isinstance(declaration.get(key), str):
                raise ValueError("Malformed formal declaration")
        names.append(declaration["name"])
        if declaration["kind"] == "theorem" and declaration["body"]:
            raise ValueError("Theorem proof leaked into formal context")
    if len(set(names)) != len(names):
        raise ValueError("Duplicate formal declaration")
    result["declarations"].sort(key=lambda d: d["name"])
    result["axioms"] = sorted(set(result["axioms"]))
    return result


def protected_sources(engine, work):
    failures = []
    support = engine.directory / engine.config["inputs"] / "support/Research"
    for source in support.rglob("*.lean"):
        target = work / "Research" / source.relative_to(support)
        if not target.is_file() or source.read_bytes() != target.read_bytes():
            failures.append(str(target.relative_to(work)))
    return failures


def extract(engine, condition, label, *, evaluation=False):
    engine.guard()
    root = engine.directory / condition
    work = root / ("evaluation-workspace" if evaluation else "workspace")
    output = root / "formal-audit" / label
    output.mkdir(parents=True, exist_ok=False)
    ownership(output)
    before = source_hashes(work)
    process = subprocess.run([
        *engine.container(condition, workspace=work, output=output, offline=True),
        *mount(TOOLS / "ExtractContext.lean", "/trusted/ExtractContext.lean", True),
        engine.image, "bash", "-lc", "lake build && lake env lean /trusted/ExtractContext.lean",
    ], capture_output=True, text=True, timeout=240)
    save(output / "compiler.log", process.stdout + process.stderr)
    if process.returncode:
        raise FormalizationFailure("Formal-context elaboration failed:\n" + process.stdout + process.stderr)
    context = parse_extraction(process.stdout)
    if source_hashes(work) != before:
        raise RuntimeError("Sources changed during formal extraction")
    context["sources"] = before
    context["environment"] = {
        "lean_toolchain": (work / "lean-toolchain").read_text().strip(),
        "manifest_sha256": hashlib.sha256((work / "lake-manifest.json").read_bytes()).hexdigest(),
    }
    # This fingerprint binds actual source, dependencies, axioms and formal meaning.
    context["candidate_hash"] = fingerprint(context)
    unapproved = sorted(set(context["axioms"]) - STANDARD_AXIOMS)
    policy = {"schema_version": 1, "unapproved_axioms": unapproved,
        "protected_source_failures": protected_sources(engine, work),
        "candidate_hash": context["candidate_hash"]}
    policy["passed"] = not unapproved and not policy["protected_source_failures"]
    save(output / "context.json", context)
    save(output / "audit.json", policy)
    return context, policy


def protected_declarations(before, after):
    """The prover may add lemmas and fill proofs, not change the formalizer's claim."""
    indexed = {x["name"]: x for x in after["declarations"]}
    changed = []
    for item in before["declarations"]:
        current = indexed.get(item["name"])
        if current is None or any(current[key] != item[key] for key in ("type", "body", "kind")):
            changed.append(item["name"])
    return changed


def translation_bundle(context, statement):
    declarations = {item["name"]: item for item in context["declarations"]}
    for target in statement["targets"]:
        if target not in declarations or declarations[target]["kind"] != "theorem":
            raise ValueError("Target is absent or is not a theorem: " + target)
    for name in statement["construction_names"]:
        if name not in declarations or declarations[name]["kind"] not in {"definition", "inductive"}:
            raise ValueError("Construction is absent or is not a definition or inductive type: " + name)
    # No source paths, comments, task text, condition, handoff prose, or proof terms.
    pending = list(statement["targets"] + statement["construction_names"])
    relevant = set()
    while pending:
        name = pending.pop()
        if name in relevant or name not in declarations:
            continue
        relevant.add(name)
        pending.extend(declarations[name].get("dependencies", []))
    value = {"schema_version": 1, "candidate_hash": context["candidate_hash"],
        "targets": statement["targets"], "construction_names": statement["construction_names"],
        "declarations": [declarations[name] for name in sorted(relevant)], "environment": context["environment"]}
    if len(json.dumps(value)) > 300000:
        raise RuntimeError("Formal context exceeds the declared complete-context limit")
    return value
