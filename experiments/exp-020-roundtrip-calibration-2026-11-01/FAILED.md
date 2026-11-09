# Calibration infrastructure failure: bind-mount root ownership

The first translator completed, but the trusted permission-export helper tried
to chmod the host-owned /output bind-mount root from the container's non-root
uid. The helper stopped before writing metrics. No judge/direct-critic ran.

The helper now changes permissions only on actor-owned files and directories;
host-owned bind roots and logs are already accessible by their host owner.
An actual uid-1100 Docker canary tests this boundary before another model run.
All inputs, partial reports, and diagnostics remain preserved.
