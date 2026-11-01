# Live dot-product proof pipeline test

Both conditions built new valid proofs and were accepted on their first pass.

| Metric | Stateless | Retrieved |
| --- | ---: | ---: |
| Accepted | yes | yes |
| Passes used | 1 | 1 |
| Lean + scans | pass | pass |
| Critic requirements | 6/6 | 6/6 |
| Builder time | 59.939s | 83.961s |
| Critic time | 63.946s | 63.290s |
| Proof-loop wall time | 151.471s | 175.186s |

Times cover the proof loop and exclude preflight/connectivity, queue wait, and cleanup. The retrieved builder opened the generic frozen Lean artifact and recorded its influence; this single pair shows no speed or pass-count advantage from that memory.

This exercised the complete proof-building pipeline, including the actual archived coordinator and workers, trusted Lean verification, independent LLM criticism, result collection, completed-pair comparison, and full-text artifact search. Both jobs began without a completed dot-product proof. All five supplied prerequisite modules were unchanged at completion.

The live test exposed one infrastructure defect: generated job artifact indexes were initially included among frozen inputs. Experiment exp-016 preserves the interrupted run. After the fix and a regression test, the new experiment completed both conditions.

Final checks: 72 pipeline tests passed; the 8,036-job repository build and placeholder/custom-axiom scans passed; frozen-input checks, result search, and diff checks passed. API cost is unknown.
