# Exponential moments on a nonnegative spectral subspace

For commuting Hermitian matrices G,H, a nonnegative real a and the closed
projection \(J=\mathbf1_{[0,\infty)}(G)\),
\[
Je^{a(H-G)}J\le e^{aH}.
\]
Consequently, if \(\rho\ge0\) and \(J\rho=\rho\), then
\[
\operatorname{ReTr}(\rho e^{a(H-G)})
\le\operatorname{ReTr}(\rho e^{aH}).
\]
No full-space positivity of G is assumed. The trace weight need not be
normalized or commute with either observable. Zero weights, zero eigenvalues
and empty ambient coordinate sets are included.

The proof uses the actual joint spectral projections of G and H. On the
nonnegative part of G the scalar exponential decreases by a nonnegative
amount; outside that part the compressed left side vanishes. The supported
trace inequality follows by positivity of the trace pairing and cyclicity.

These are the auxiliary spectral inequalities used in the rough component
estimate in the September 24, 2026 area-law manuscript,
[Section 7, lines 553–555](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/07-comparators.tex#L553-L555).
For the physical application, G is the actual operator F_Q+F_V−F_Y on
three independent physical factors, H is the sum of the two actual merge
deficits, and the component density must first be shown to lie in J.
The present generic inequalities do not assume those identifications or
claim the full component compression estimate.
