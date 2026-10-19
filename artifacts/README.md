# Proof artifacts

This directory is the repository's searchable external memory.

New experiment summaries live in `../experiments/<id>/artifacts/`, next to their
evidence. This directory provides the cross-experiment index and validated lessons.
The executable runner belongs in `../pipeline/`; raw logs stay with the experiment.

- `runs/` retains older standalone proof-attempt records.
- `validated/` contains compact lessons supported by verified runs.
- `index.md` is the retrieval entry point.

Repository agents follow the protocol in [`../AGENTS.md`](../AGENTS.md).
Project-specific narrative logs can remain under `projects/<project>/runs/`;
artifact records link to them rather than replacing them.

For memory-ablation experiments, stateless runs must not read this directory.
Retrieved runs must use a frozen snapshot and list every artifact ID opened.
Experiment-local artifacts and prior submissions are also excluded from stateless runs.
Artifacts created by either condition remain private to that run until the
comparison finishes, preventing the second condition from learning the first
condition's result.
