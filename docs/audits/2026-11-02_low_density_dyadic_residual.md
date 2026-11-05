# Geometric residual decay at the actual ceiling scales

For C ≥ 100, u ≥ 1 and 0 < g ≤ 1, define
ell_i = ceil(C (u + i log 2)^2/g). The proved scalar estimates give
ell_i ≥ ell_0 + 64 i and, for every real eta,

    exp(−(ell_i − eta)/8) ≤ exp(−(ell_0 − eta)/8) / 2^(4i).

The ceiling estimate uses Mathlib monotonicity and exact translation by
the natural integer 64 i. No separate positive-index case or rounding
loss is needed. The exponential estimate uses the same actual ceilings.

These are supporting numerical estimates for the low-density accuracy
refinement in ALVV, arXiv:1602.08828v2. The physical comparison must still
be applied at these scales; a fixed-error original/clipped comparison
cannot be iterated as though it had arbitrary accuracy. This module does
not state an entropy or sharp MPS approximation theorem.
