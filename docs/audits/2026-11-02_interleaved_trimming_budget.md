# Reference budgets before large target overlap

The weighted reference-trimming expression can be controlled even when the
filtered error is close to one. For $0<a\le1$, use
$\theta=a/64$, reference accuracy $\varepsilon\le a^2/16384$ and threshold
error $\tau\le a/256$. For every normalized filtered error $0\le f\le1$,
the full weighted expression is at most $f+a/16$.

The scalar proof does not identify the target with the original ground space,
construct a physical filter, or choose an initial successful Haar sample.
If the target is a clipped low-energy space, its comparison with the original
ground space is a separate error budget. In particular, reducing the reference
error alone cannot remove a fixed error in that comparison.

The Mathlib-only module `InterleavedTrimmingParameters` passed a strict
actual-module check in 4.450 s, with no QIC dependency. The checked provider
was TN `f7bae89a06741bb61820b50cd4b421a2d42951e7` with its own QIC
`00ca963e4a79afd68d9d6f875dd468a21f1dccdd`. Sources, root inputs and the
warmed Mathlib object were guarded before and after the check. The imported
foundation inspection was shared with the actual interval application and
is recorded in the accompanying manifest. No cache or provider was changed.

The theorem is a numerical auxiliary for the reference argument in ALVV,
arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670, and
lines 1801–1805. It does not establish the physical parameter substitution,
adaptive sampling probability or running time.

The imported twelve-name inspection, including this scalar theorem and all
actual interval consumers, passed in 5.171 s with 140 guarded source/object
pairs. Every inspected declaration uses only `propext`, `Classical.choice`
and `Quot.sound`. The temporary inspection source was deleted. Blueprint
source synchronization, reader-facing prose and whitespace checks passed.
The combined ordinary build and compiled blueprint check remain required.
