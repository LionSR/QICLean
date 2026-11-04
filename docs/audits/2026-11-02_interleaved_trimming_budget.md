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

The theorem is a numerical auxiliary for the reference argument in ALVV,
arXiv:1602.08828v2, Figure `fig:merge-prime`, lines 1668–1670, and
lines 1801–1805. It does not establish the physical parameter substitution,
adaptive sampling probability or running time.
