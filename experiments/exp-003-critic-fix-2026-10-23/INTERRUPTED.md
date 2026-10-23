# Interrupted; do not pool with the restarted comparison

On 2026-10-23 the user requested doubling the critic limit for both conditions
and restarting from the beginning. This run used the original 120-second critic
budget. Its controller and active retrieved builder were stopped; existing inputs,
candidate files, transcripts, reports, and measurements are retained as-is.

The stateless condition used two builder passes. Both offline builds passed.
The first critic rejected an incomplete proof through the new early checkpoint;
the second wrote a final pass report but hit its process time limit, so the
controller recorded an infrastructure error rather than accepting the result.
The retrieved condition had advanced to its second builder pass when stopped.

This is not a completed paired comparison. Do not infer a memory benefit from it
or reuse its same-target code in the restart. The restart is a fresh experiment
using the original inputs and approved memory snapshot, with 240 seconds per
critic, 180 seconds per builder, and at most two passes per condition.
