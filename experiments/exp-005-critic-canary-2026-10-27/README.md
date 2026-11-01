# Critic contract canary

This is an infrastructure canary, not a memory-ablation comparison and not a
new proof attempt. It re-reviews two frozen, previously verified candidates with
the active critic contract.

Pre-registered expectations:

- `canary-incomplete`: the exp-004 stateless pass-two candidate must produce a
  valid `checkpoint.json` completeness rejection and be stopped by the watcher.
- `canary-complete`: the original pilot stateless candidate must produce a valid
  final `review.json` with overall verdict `pass` and exit cleanly.

Fixed settings: `gpt-6.1-sol`, medium reasoning, 240 seconds per critic. Critics
receive the original source, private rubric, candidate, and saved trusted
verification evidence. They receive no builder transcript or retrieval memory.
The verification command associated with both candidates is
`bash pipeline/verify.sh`; this canary does not modify either candidate.

Acceptance requires both expectations. A timeout, crash, malformed report,
wrong phase/filename, or unexpected verdict fails the canary. Unknown usage and
cost remain unknown. Raw evidence is preserved under each condition's `review/`.
