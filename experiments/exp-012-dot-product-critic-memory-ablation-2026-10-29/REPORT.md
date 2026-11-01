# Dot-product critic memory-ablation report

The paired experiment produced the same perfect pass/fail accuracy in both
conditions, but different defect-category specificity.

| Metric | Stateless | Retrieved |
| --- | ---: | ---: |
| Correct verdicts | 6/6 | 6/6 |
| Expected defect categories | 3/4 | 4/4 |
| False passes | 0 | 0 |
| False rejections | 0 | 0 |
| Invalid reports | 0 | 0 |
| Timeouts | 0 | 0 |
| Critic wall time | 238.393 s | 295.541 s |

The stateless critic correctly rejected the additions-only candidate, but used
only the broader `missing-final-theorem` label and missed the preregistered
`missing-exact-product-link` category. The retrieved critic reported both and
also identified `wrong-error-count`.

Retrieved was 57.148 seconds (24.0%) slower. Every retrieved run opened at
least one approved artifact and wrote a valid retrieval audit log; no stateless
run received the memory mount or wrote such a log.

The strict experiment status is **partial** because the preregistered acceptance
test required both modes to find all four expected categories. This single
paired sample does not establish that retrieval caused the category difference.
The retrieved additions-only log says memory influenced stable-ID/report
discipline; it does not claim the artifact supplied the mathematical insight.

All 12 candidates passed the trusted Lean gate. After the run, 60 pipeline tests
and the repository-wide 8,036-job Lean build plus placeholder/custom-axiom scans
also passed.
