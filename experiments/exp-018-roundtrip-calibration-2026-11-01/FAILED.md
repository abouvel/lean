# Calibration infrastructure failure: atomic-report permissions

All six candidates passed offline builds, protected-source checks, and the
transitive axiom audit. The first blind translator completed normally and wrote
translation.json atomically using a temporary file with mode 0600. The host user
could not read the file produced by the container's uid, so validation stopped
before any round-trip judge or direct-critic call. This is not a semantic fail.

The frozen experiment and raw evidence are preserved. The trusted session
runner now normalizes exported output permissions and rejects symlinks; the
production-role wrapper also normalizes candidate source files. A regression
test covers owner-only atomic writes. A fresh calibration uses the same already
verified candidate sources, expected labels, and extracted formal contexts.
