# Frozen infrastructure failure before critic launch

All six candidates passed the unfrozen offline preflight. The experiment then
froze successfully, but the repeated guarded verification stopped before any
critic call: Docker had created `.lake/packages` as a root-owned mount-point
directory during preflight, and the second workspace permission preparation
could not change it.

No critic or model call occurred. This experiment remains frozen and failed.
The next run uses a new ID and creates the package mount point explicitly before
either verification pass.
