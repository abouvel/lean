# Runtime source snapshot

These are byte-identical copies of the pipeline files hashed in this run's
original `frozen-manifest.json`, saved before the later critic fix. The manifest,
prompts, candidates, metrics, and results were not rewritten. The historical
checker verifies these archived bytes against the original hashes; task inputs
are still checked in their original locations. New runs use the active pipeline.

This snapshot preserves source provenance, not a new run or a completed proof.
