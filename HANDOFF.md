# Research pipeline: agent handoff

Updated: 2026-10-27. Read `AGENTS.md` first; it governs repository work.

## Start here

Immediate priority: fix the critic report contract before another paid run. The
latest pair had no accepted result: stateless hit a report-schema error; retrieved
failed final compilation. This documentation request does not authorize a run.

**Supervisor context only. Do not give this file to experimental builders.** It
contains prior results and proof locations. Reading it contaminates a fresh
stateless subject; launch evaluated subjects through the isolated pipeline.

## Research goals and user preferences

The user researches agent-assisted floating-point proofs in Lean under Karthik
Duraisamy, with discussions involving Sahil. They are new to Lean and need clear
explanations of statements, assumptions, and what each check establishes.

1. Formalize binary-tree reduction and its floating-point error analysis.
2. Compare no-external-memory agents against agents retrieving curated artifacts:
   success first, then time, compiler work, tokens, and cost.

Artifacts are external memory, not model-weight updates. Plasticity, post-training,
and richer multiagent systems are future questions. No learning or savings benefit
has been established. Prefer modular code, concise documentation, clear diagrams,
and experiment-local evidence. Do not recreate root `projects/` or `artifacts/`.
Keep implemented behavior distinct from proposals.

## Environment and Git baseline

- WSL: Ubuntu, user `abouvel`, repository `/home/abouvel/fall26/research`.
- Windows: `\\wsl.localhost\Ubuntu\home\abouvel\fall26\research`.
- Host shell is PowerShell; execute the pipeline through WSL/Linux.
- Branch: `pipeline`; inspected HEAD: `a42eeb51fa8a9ee36f5a6027bd840189198ab283`.
- Working tree was clean before this handoff; earlier work has been committed.
- Lean and Mathlib pinned to `v4.28.0`; WSL Python 3.10, standard-library runner.
- Runtime tag: `research-proof-pilot-ready:2026-10-19`.
- Recorded image ID: `sha256:8c6dc3e8d16fcf0da6174cc5ecd8ca1e0b964909520d2b79ca0b272ebaa1bad9`.

Recheck Docker availability and `runtime.json` before execution. Tags and package
installation are not fully immutable. WSL rg was unavailable; grep/find are valid
fallbacks. Prefer WSL Git over modifying global safe-directory settings.
Never print `.env`, credentials, or authentication contents into records. Never
stop unrelated containers or use global Docker prune commands.

PowerShell example:

```powershell
wsl -d Ubuntu -u abouvel -- bash -lc 'cd /home/abouvel/fall26/research && python3 -m unittest discover -s pipeline/tests -v'
```

## Repository map

```text
AGENTS.md                   Governing rules
HANDOFF.md                  Supervisor context, never subject input
README.md                   Overview, chiefly the original successful pilot
lean-toolchain              Compiler pin, required
lakefile.toml               Configuration; srcDir = lean
lake-manifest.json          Dependency lock, required
lean/Research.lean          Library import entry point
lean/Research/
  DotProduct.lean
  Common/FloatingPoint/     Relative-error Model and Gamma lemmas
  Projects/BinaryTreeReduction.lean
  Projects/BinaryTreeReduction/
    Tree.lean               Trees, leaves, depth, perturbations
    Algorithm.lean          Pairing, invariants, termination
    Reduction.lean          Rounded reduction and backward error
    DotProduct.lean         Rounded products plus reduction error
    Examples.lean           Acceptance traces
pipeline/                   Shared runner, verifier, critics, Docker, tests
experiments/
  dot_product/              Earlier work
  exp-001-binary-tree/      Original successful pilot and input template
  exp-002-bounded-2026-10-23/
  exp-003-critic-fix-2026-10-23/
  exp-004-critic-240s-2026-10-23/
```

The reusable library is NOT starting input for fresh experimental agents.
Research is the module namespace, not a redundant root project folder.

Each experiment owns `inputs/` (source/prompt), `evaluator/` (private rubric and
protected config), `memory/` (frozen snapshot), `artifacts/` (JSON/Markdown records,
index, candidate lessons), and any notes/slides. Config, frozen manifest, and
runtime files preserve provenance; `comparison.json` and `REPORT.md` give results.

Bounded evidence layout:

```text
<condition>/passes/pass-NNN/
  pass.json                 Controller outcome
  frozen-inputs.json        Staged hashes
  feedback/feedback.json    Own earlier feedback, if present
  <condition>/
    workspace/Research/Submission.lean
    output/                 Builder prompt, events, metrics, retrieval
    evaluation-workspace/   Clean offline copy
    evaluation/             verification.json and verification.log
    reviewer-spec/          Private critic inputs
    review/                 Critic reports, events, metrics, extra checks
```

Single-shot exp-001 uses condition/workspace, output, evaluation, and review
directly, without pass subdirectories.

## Mathematical target and scope

The isolated task is Sahil Bhola's Algorithm 1 and Theorem 3.1, in exp-001's
`inputs/source.pdf` and `source.txt`. Read those before asserting an exact theorem.
Do not confuse this with the separate probabilistic dot-product theorem from chat.

Split the active forest at its ceiling half length, combine corresponding slots
from the two halves, and carry an unmatched subtree unchanged. This is NOT
adjacent-pair reduction. Reviewer-only acceptance trace:

```text
[2,3,4,5,6] -> [7,9,4] -> [11,9] -> [20]
```

For every nonempty input, establish one final tree, occurrence/multiplicity
preservation (including duplicates), exact sum preservation, and depth at most
`Nat.clog 2 n`. A carry gains no addition node and no rounding call.

Abstract numerical model:

```text
round(z) = z*(1+delta), |delta| <= u
gamma(L,u) = L*u/(1-L*u), assuming L*u < 1
```

The deterministic backward-error result expresses computed output as an exact
sum of perturbed ORIGINAL inputs, with componentwise gamma bounds controlled by
logarithmic path depth. A bound for output-tree leaves is insufficient unless
their occurrence-preserving connection to the original inputs is proved.
The reusable dot-product proof separately adds one rounded multiplication per
leaf, producing a depth-plus-one bound on product values.

Existing library declarations include `reductionTree_spec`,
`reductionTree_exactSum`, `finalForest_preserves_inputs`,
`finalForest_depth_le`, and `algorithm1_exists_perturbation`. Do not expose their
implementations to fresh baseline subjects.

Scope excludes IEEE 754 bit behavior, runtime overflow/underflow detection,
physical parallel scheduling, and the separate probabilistic theorem. Exact
example traces demonstrate shape, not measured floating-point error.

## Inputs and memory conditions

Both builders start with `import Mathlib` and protected build infrastructure.
Both receive the original paper and extracted text, including its mathematical
proof and pseudocode: this is source-assisted formalization, NOT proof discovery
from a bare conjecture. No supplied Lean theorem skeleton, tactics, proof recipe,
worked example, existing project proof, prior chat, or run artifacts goes to the
first builder. The acceptance trace above is withheld from builders.

Retrieved additionally receives frozen artifact `pilot-general-lean-001`:
generic absolute-value, denominator-positivity, and stale-import/rebuild advice.
It excludes the target proof. Its provenance is prior work on this assignment;
this is not unseen-task transfer evidence.

The current protocol does NOT automatically transfer newly generated stateless
artifacts to retrieved. It uses pre-existing curated memory. A different transfer
protocol needs its own definition and answer-leakage review.

## Implemented architecture

Bounded mode completes stateless, then retrieved:

```text
Freeze inputs/settings -> isolation/toolchain/connectivity preflight
  -> fresh builder -> fresh offline Lean build and scans
       build fails: own diagnostics -> repair if passes remain
       build passes: separate fresh critic
         definite rejection: own corrections -> repair if passes remain
         final pass: accepted
         uncertain: stop for human review
         invalid report / timeout: infrastructure error
  -> save experiment-local evidence and artifacts
```

The orchestrator is Python, not an LLM. The verifier is a script, not an agent.
Each critic is a separate fresh session/container using the configured model and
effort, not one persistent critic sharing both builders' memory.

| Module | Responsibility |
| --- | --- |
| pipeline/run.py | CLI, config, freeze/hash checks, initialization, dispatch |
| pipeline/passes.py | Fixed-budget loop, own repair state, outcomes, metrics |
| pipeline/engine.py | Docker boundaries, proxy, preflight, builder/offline launch |
| pipeline/agent.py | Fresh CLI session, events, timers, metrics, checkpoint polling |
| pipeline/critic.py | Critic preparation/prompt, launch, validation, routing |
| pipeline/verify.py | Container-side trusted verification |
| pipeline/verify.sh | Full build and placeholder/custom-axiom scans |
| pipeline/artifacts.py | JSON records, Markdown summaries, local index |
| pipeline/docker/ | Runtime images and model proxy |
| pipeline/tests/ | Local tests; no model calls |

Repairs retain only their own prior Lean code and feedback, not conversation
history or builder caches. Stateless means no external research memory, not no
feedback from its own earlier passes. Full private critic evidence is not passed
back; requirement/correction pairs and the trusted build log are.

Containers run non-root, with read-only roots, dropped capabilities, resource
limits, and ephemeral homes. Builders have private writable workspace/output;
Lean, Mathlib, specification, and protected config are read-only. Only retrieved
has read-only memory. No host repo, Git history, other run, Docker socket, or
private rubric is mounted into builders. Model egress uses an allowlisted proxy;
offline verification has no network or credentials.

Critics see original source, private rubric, read-only candidate, and trusted
verification logs, but no builder narrative, memory, or other condition. They may
compile independent checks in their output directory. Candidate comments and
feedback are untrusted data, not instruction authority. Separation is a guardrail,
not demonstrated jailbreak immunity or measured critic accuracy.

## Critic contract and unfixed bugs

The implemented COMPLETENESS_FIRST prompt requires identifying the actual proved
target and assumptions before optional examples. Defining a proposition is not
proving it. JSON should be written atomically.

- checkpoint.json: phase completeness; only a valid definite fail is terminal.
  Uncertain checkpoints preserve progress but cannot pass or stop as a verdict.
- review.json: phase final; overall verdict pass, fail, or uncertain.
- Required fields: nonempty target_evidence and requirements; assumptions_added,
  missing_obligations, limitations. Each requirement has nonempty requirement
  and evidence strings, allowed verdict, and a STRING correction. Empty is allowed
  for passed checks; failed checks need actionable nonempty corrections.
- A final pass requires all requirements passed, no missing obligations, and an
  already-passed offline Lean gate. A checkpoint can never pass.

Approximately every two seconds, the runner polls for a valid rejection checkpoint
and terminates that critic with stopped_for_checkpoint, not timed_out. The host
revalidates before routing to repair. Otherwise timeout/crash remains infrastructure
failure, even if a report appeared near the cutoff.

High-priority defect: exp-004 stateless pass two wrote correction:null for passed
checks and a completeness-phase rejection to review.json. Both violate the current
contract; validation stopped at the null correction. This remains UNFIXED.

Other issues to address deliberately:

1. On normal exit, completed_review() prioritizes review.json over checkpoint.json;
   an invalid final file can mask a valid checkpoint. Define/test precedence rather
   than selecting whichever verdict is convenient.
2. A report can be saved before process timeout (exp-003). A future final-report
   watcher requires strict validation and symmetric pre-registered rules. Never
   simply ignore timed_out or retroactively accept that historical result.
3. run.py check prints unknown bounded summary fields because its display assumes
   legacy single-shot records. Hash validation still runs; inspect comparison.json.
4. passes.total() reports unknown critic time when a pass never invokes a critic.
   Distinguish known skipped stages from invoked stages with missing measurements.
5. Pipeline README still mentions 120-second critics and says live validation of
   the revised critic is pending. Current config is 240 and trials have occurred.
6. Artifact indexes may have entries above their heading and terse metadata.

## Run history and conclusions

Use each run's frozen config/report, not today's template, for historical budgets.

| Experiment | Outcome |
| --- | --- |
| exp-001-binary-tree (2026-10-19) | Original single-shot pilot: 1,200-second builders, 300-second critics. Both passed offline Lean and separate critics, including independent checks. Retrieved builder was 17.2% slower in this one pair. |
| exp-002-bounded-2026-10-23 | Two-pass cap, 180-second builders, original 120-second critics. Both initial submissions compiled; both critics timed out without structured verdicts. Infrastructure errors stopped each after pass one. Post-run inspection found the full backward-stability proposition defined but not proved. |
| exp-003-critic-fix-2026-10-23 | New completeness-first critic, 180/120-second budgets. Stateless initial rejection triggered repair; second submission compiled and critic wrote pass, but process timed out so no acceptance. User requested restart; retrieved was stopped during second builder pass. Incomplete pair, not pooled. See INTERRUPTED.md. |
| exp-004-critic-240s-2026-10-23 | Fresh restart, 180-second builders, 240-second critics, two passes each. No critic timeouts. Stateless: both builds passed, final critic report invalid. Retrieved: first build passed and was rejected; final build failed. Neither accepted. |

Reports are experiment-local REPORT.md files; exp-003 has INTERRUPTED.md. Failed
and interrupted evidence must remain intact, not deleted after later successes.

Original pilot measured builder times: 458.993 seconds stateless, 538.043 seconds
retrieved. Compiler-command events: 24 vs 27. Cumulative input tokens: 1,278,341 vs
1,660,099, including cached subsets. Monetary cost unknown. These are one-pair
observations, not population performance estimates or proof of harmful retrieval.

Latest exp-004 metrics:

| Metric | Stateless | Retrieved |
| --- | --- | --- |
| Passes | 2 | 2 |
| Offline gates passed | 2/2 | 1/2 |
| Condition wall time | 530.18 s | 452.66 s |
| Builder compiler-command events | 16 | 14 |
| Critic durations | 76.045 s; 67.092 s | 68.034 s |
| Aristotle calls | 0 | 0 |
| Complete token/cost totals | unknown | unknown |

All four builders reached 180 seconds. Shorter retrieved wall time includes
skipping its final critic after compilation failure: do NOT call it a saving.
The aggregate retrieved critic time is unknown in machine metrics because the
second pass had no critic, despite the first duration being known.

Retrieved's final build failed at Submission.lean:353:47 in a duplicate example:

```text
2 ::_m 2 ::_m 2 ::_m 2 ::_m {2} = [2,2,2,2,2] coerced to a multiset
```

See the exact Unicode goal and compiler output in its pass-two
retrieved/evaluation/verification.log. This does not disprove the mathematical
theorem, but blocks acceptance of the whole submission. Do not repair/remove the
example in historical evidence and relabel the original experiment successful.

Warranted conclusions: recorded isolation checks passed; early completeness
rejections triggered repairs; Lean and semantic review catch different failures;
report reliability remains a bottleneck. No established artifact success, cost,
or learning benefit; no measured critic calibration or jailbreak resistance.
No human sign-off is claimed. No validated lessons were promoted from these
bounded runs.

## Aristotle

Aristotle generates proofs; it is not the Lean correctness gate or semantic critic.
Policy permits delegation only for an isolated blocked lemma after its statement
compiles and local repair/decomposition has been attempted. Preserve the statement
and verify any returned proof locally.

Automatic delegation is NOT implemented: the runner rejects enabled Aristotle
configs. These experiments made zero calls. Neither a critic rejection nor Lean
failure automatically invokes it. Future integration requires equal eligibility,
call budgets, provenance, and timeouts across conditions.

## Artifacts, preservation, and fair evaluation

Follow the full schema/promotion rules in AGENTS.md. For normal proof development,
read the relevant artifact index and validated lessons. For experimental subjects,
condition restrictions supersede ordinary retrieval. Log opened artifact IDs,
queries, and concrete decisions influenced; access alone is not causal benefit.

Keep original inputs, candidates, transcripts, and reports unchanged. Summaries
stay experiment-local. Candidate lessons are unvalidated until their supporting
work passes verification and the generalization/limitations are reviewed. Freeze
snapshots before assignment; exclude target proofs and answer-bearing material.
No cross-condition feedback, mid-run budget changes, or extra passes after caps.
Unknown usage/cost stays unknown. Report regressions and failures too.

Important before editing shared code: manifests hash execution-time pipeline
source as well as inputs/config. Preserve matching original runtime bytes under
that experiment's runtime-source/pipeline/... and verify against existing hashes.
Exp-002 already has a snapshot. Exp-003/004 may need snapshots before the next
pipeline change. The checker supports archived runtime files but still checks
task inputs in original locations. Never regenerate old hashes just to pass.

Exp-001 relocation.json maps older paths and checks historical pipeline bytes in
Git; keep that history. A starting commit alone may omit then-uncommitted code;
frozen source hashes and image provenance matter.

Compiler-command events are not lemma attempts. About 8,036 library build jobs
are NOT 8,036 experiments, independent tests, or Aristotle calls. Cached inputs
are a subset of cumulative input tokens. Do not add potentially overlapping
reasoning/output counters. Never invent monetary savings from login-based usage.

## Verification and commands

Freshly checked on 2026-10-27: **46 local tests passed; full Lean build passed
(8,036 jobs), with placeholder/custom-axiom scans passing.** This checks the
existing library, not the failed isolated retrieved candidate. Only this Markdown
file was added during handoff preparation; no paid models were called.

From WSL repository root, no model calls:

```bash
python3 -m unittest discover -s pipeline/tests -v
bash pipeline/verify.sh
python3 pipeline/run.py check --config experiments/exp-004-critic-240s-2026-10-23/experiment.json
```

verify.sh builds the project and scans sources for sorry/admit/custom axioms.
It fails on missing sources or scan errors and supports both lean/Research and
isolated Research layouts. Compilation alone does not establish intended meaning.

Only when authorized to spend model quota, use a NEW experiment name:

```bash
python3 pipeline/run.py run --config experiments/exp-001-binary-tree/bounded.json --name exp-005-report-contract-YYYY-MM-DD
```

Current template: gpt-6.1-sol, medium reasoning, two passes, builder 180 seconds,
critic 240 seconds, Aristotle disabled. Check Docker, dependencies, authentication
availability, and exact config first. New runs freeze their own copies.

run calls models; check does not. replay rebuilds saved single-shot candidates
offline without rerunning critics. Its current source-copy path is legacy: do
not assume replay selects the final bounded candidate automatically. Inspect and
test that behavior before replaying bounded runs. Existing names are rejected.

## Recommended next steps, not yet executed

1. Preserve runtime provenance before edits. Fix critic prompt and schema together:
   explicit typed JSON examples, correction rules, atomic writes, unambiguous
   checkpoint/final routing. Keep acceptance fail-closed.
2. Add local cases matching exp-004's null corrections and wrong phase/filename,
   plus missing, partial, contradictory, uncertain, timed-out, and near-deadline
   reports. Decide precedence explicitly; do not reinterpret old outcomes.
3. Test report generation/validation before expensive proof pairs. Constrained
   structured output is an option only after checking the chosen runner's actual
   interface; do not assume it supports a feature.
4. Fix bounded display/metrics and stale README wording without rewriting frozen
   historical prompts. Improve indexes if needed through the writer.
5. Run local tests and the full Lean gate, then explain what changed and what is
   still unmeasured. Obtain authorization for another paid pair if not requested.
6. Pre-register equal-budget clean-subject comparisons, then expand to several
   comparable, preferably matched distinct tasks. Compare success first, then
   cost/time among comparable outcomes. Do not pool interrupted/changed protocols.

If the user instead prioritizes mathematical completion, work in a separate new
development attempt with artifact provenance. Do not conflate assisted repair of
a known candidate with an uncontaminated stateless benchmark.

The next agent should confirm branch/dirty state and the user's desired next
action, state the report-contract bug plainly, and offer the smallest testable
fix. Do not restart experiments merely because conversation context is missing.
