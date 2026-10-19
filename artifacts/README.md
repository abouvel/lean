# Proof artifacts

This directory is the repository's searchable external memory.

It is not the experiment workspace. Keep summaries and reusable lessons here;
link to the full inputs, code, transcripts, and metrics in `../experiments/`.
The executable runner belongs in `../pipeline/`.

- `runs/` contains factual records of individual proof attempts.
- `validated/` contains compact lessons supported by verified runs.
- `index.md` is the retrieval entry point.

Repository agents follow the protocol in [`../AGENTS.md`](../AGENTS.md).
Project-specific narrative logs can remain under `projects/<project>/runs/`;
artifact records link to them rather than replacing them.

For memory-ablation experiments, stateless runs must not read this directory.
Retrieved runs must use a frozen snapshot and list every artifact ID opened.
Artifacts created by either condition remain private to that run until the
comparison finishes, preventing the second condition from learning the first
condition's result.
