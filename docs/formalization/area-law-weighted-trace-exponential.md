# Weighted exponential traces in the rough comparator estimate

The rough estimate in the pinned September 24, 2026 manuscript, `07-comparators.tex`, lines 553–555, combines the two exponential merge factors by Cauchy–Schwarz. A separate arithmetic-mean inequality suffices to combine polynomial bounds for their doubled moments:

$$\operatorname{Re}\operatorname{tr}(\rho e^{a(A+B)})\le\frac{\operatorname{Re}\operatorname{tr}(\rho e^{2aA})+\operatorname{Re}\operatorname{tr}(\rho e^{2aB})}{2}.$$

Here $A$ and $B$ are commuting Hermitian matrices, $\rho$ is any positive semidefinite matrix on their common finite coordinate set, and $a$ is any real number. No trace normalization or commutation with $\rho$ is required. The proof expands the nonnegative weighted trace of $(e^{aA}-e^{aB})^2$. Empty coordinate sets and the zero weight are included.

The formal theorem is `Matrix.PosSemidef.re_trace_mul_exp_add_le_half_sum` in `QICLean/Analysis/WeightedTraceExponential.lean`. It is an auxiliary arithmetic-mean bound, distinct from the printed geometric-mean estimate. To apply the accepted merge moments, their exponent range must contain $2a$; in the intended range, $0\le a\le1/2$ suffices. The actual common-space definitions and commutation of the two merge deficits, and the remaining physical comparison steps, are separate mathematical obligations.
