# Interrupted before critic launch

The first local Lean preflight began cloning and rebuilding Mathlib inside the
`known-complete` fixture because the generated workspace did not reuse the
repository's pinned package mount. The process was stopped. No critic or model
call occurred, no expected label was exposed, and no result from this directory
should be scored.

Cleanup through the Windows UNC path was not completed because recursive removal
could traverse package repositories or links. The partial directory is preserved
as failed setup evidence. The corrected run uses a new experiment ID and verifies
candidates in the existing isolated container environment.
