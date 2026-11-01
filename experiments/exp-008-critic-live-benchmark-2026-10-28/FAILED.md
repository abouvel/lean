# Frozen infrastructure failure before critic launch

All inputs and expected labels were frozen, but the first offline formal gate
failed because the reviewer container could not create
`/workspace/.lake/build`. The candidate was readable; the generated workspace
had not received the disposable-workspace permissions used by the shared
pipeline. No critic or model call occurred. This frozen experiment is preserved
and must not be relabeled or resumed.

The next run uses a new experiment ID and applies the existing `ownership()`
preparation to each generated evaluation workspace before verification.
