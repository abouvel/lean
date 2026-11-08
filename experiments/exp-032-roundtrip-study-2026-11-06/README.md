# Round-trip pipeline study

The [frozen plan](plan.json) schedules three fresh trials per condition for
dot product, Horner evaluation, and forward finite differences. Each pair
uses the same source task, prerequisites, model, and role deadlines. The
retrieved condition receives the frozen, answer-excluded generic note. The
runner queues stateless jobs before retrieved jobs and uses one worker.

The launcher starts the 18 proof jobs only after the two frozen binary-tree
controls meet their expected reviewer verdicts. The control uses fixed Lean
submissions for Algorithm 1 and Theorem 3.1, with a complete case and a
compiling case missing the original-input link.

Use [job results](artifacts/jobs.md) for outcomes and `scorecard.json` for
Lean and reviewer verdicts, timing, token usage by role, and artifact use.
The primary automated outcome requires the Lean gate and agreement from
both reviewers. Expert semantic verdicts are pending until supplied as
independent candidate-bound labels. Do not interpret same-task repeats or
stateless-first timings as held-out accuracy or a causal memory benefit.
