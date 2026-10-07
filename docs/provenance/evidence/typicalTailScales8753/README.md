# A uniform typical-width tail bound

The mathematical source is frozen at `317ecbd4` and is independently written
from the pinned area-law manuscript. For fixed θ≥0 and C>0, it chooses one
N≥2 such that the source tail expression at width n^(3/5) is at most n^(-100)
for every n≥N and every 0<B≤Cn. The threshold is independent of B.

The proof first bounds the denominator uniformly, then uses Mathlib's real
power asymptotics to compare a stretched exponential with n^(-100). This
result derives neither the geometric linear-budget bound nor the spectral
tail estimate for an actual Hamiltonian. Those remain with their respective
mathematical arguments. The actual normalized-state consequences are proved
separately in the parent contribution QICLean #608.

Pinned prebuilt Mathlib cache retrieval, the linter-bearing 2,047-job target
build, strict complete-source elaboration and the exact-name kernel audit
all pass. Only `propext`, `Classical.choice` and `Quot.sound` occur. The
initial audit attempt omitted the audit-file module header and its usual
hash-command linter allowance; its failing command and raw output are
preserved separately and are excluded from successful verification.

Whole-file source and command-log hashes, actual exits and exact commands
are recorded in `checks.json` and the individual exit records. The unique
blueprint fragment states this numerical implication. Shared import/chapter
inclusion and complete library/blueprint checks remain pending.
