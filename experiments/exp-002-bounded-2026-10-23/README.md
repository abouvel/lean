# Experiment 2 — bounded builder/critic comparison

Executed on 2026-10-23. Both candidate builds passed, but both critics timed out;
neither candidate was accepted. Each condition stopped after one of two allowed
passes. The full backward-error theorem remained unproved in the submitted code.

[Read the report](REPORT.md) · [Metrics](comparison.json) · [JSON artifacts](artifacts/index.md)

Per-pass evidence is in `<condition>/passes/pass-001/`. Limits were identical:
180 builder seconds/pass and 120 critic seconds/pass. No budget was extended.
No Aristotle calls or new-artifact transfer occurred. This is not a demonstrated
memory or efficiency benefit; see the report before interpreting compilation as success.
