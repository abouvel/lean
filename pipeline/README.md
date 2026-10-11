# Initial proving pipeline

The pipeline is intentionally small. Lean is the verifier; Aristotle is an optional slow fallback.

```text
source theorem
→ reviewed Lean statement
→ compiling skeleton
→ small lemmas
→ local tactics and compiler-guided repair
→ further decomposition if blocked
→ Aristotle for one isolated blocked lemma
→ local verification
→ semantic audit and run record
```

## Aristotle rule

Submit only after the statement compiles, local search and repair have failed, and the goal is a small lemma. Send a minimal staging project with no credentials or unrelated files. Accept the result only if the theorem statement is unchanged and the main project builds without `sorry`, `admit`, or new axioms.

Use [`verify.sh`](verify.sh) for the local build. Placeholder and axiom checks remain part of the review before a result is accepted.
