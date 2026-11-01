# Five-case live Lean critic benchmark

Date: 2026-10-28. The critic got all five overall verdicts right with no false
passes, false rejections, invalid reports, or timeouts. It matched three of four
preregistered defect categories, so the strict benchmark acceptance test did
not fully pass.

| Case | Expected | Actual | Expected category found |
| --- | --- | --- | --- |
| Known complete | pass | pass | yes |
| Missing original-input link | fail | fail | yes |
| Proposition only | fail | fail | yes |
| Concrete example only | fail | fail | no |
| Conclusion assumed | fail | fail | yes |

For the concrete-example case, the critic reported `missing-final-theorem`
instead of the preregistered `concrete-example-only`. The rejection was correct,
but the category was less specific. The result was not relabeled after the run.

All five candidates passed the trusted Lean build and placeholder/custom-axiom
scans before critic launch. Critics used `gpt-6.1-sol`, medium reasoning, and a
240-second per-case limit. Aggregate recorded critic time was 192.446 seconds;
the complete case used 84.281 seconds and the four early checkpoints used
22.041–32.042 seconds each. Token usage was available only for the complete
case: 158,882 input tokens, including 128,896 cached input tokens, and 2,934
output tokens. Cost is unknown.

The first two setup attempts are preserved separately as pre-model
infrastructure failures. Neither launched a critic. They are not part of this
score.

The immediate lesson is to make the defect taxonomy hierarchical or explicitly
multi-label: a concrete-example-only candidate also lacks the requested final
universal theorem. The completed score must remain unchanged.
