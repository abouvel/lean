# Generic Lean observations

artifact_id: pilot-general-lean-001
status: curated extract of previously validated observations

- In Mathlib v4.28.0, the real absolute-value triangle inequality is named `abs_add_le`.
- For rational inequalities, establish positive denominators explicitly before clearing them and using arithmetic tactics.
- When a changed imported declaration appears missing, rebuild the imported module before assuming the declaration was never defined. Stale .olean files can hide new declarations.

These are generic proof-engineering notes. They contain no target theorem, reduction implementation, numerical example, tree invariant, or logarithmic-depth proof.
