# Buffered spectral comparisons with a derived energy shift

The new generic finite-matrix theorem starts from positive lower matrices, actual complete
orthonormal eigenbases, one normalized attained ground eigenvector of the second matrix,
mu≤e, and two actual restricted-residual estimates. It derives 0≤e−mu≤xiB internally
using the previously proved restricted-residual energy theorem. It does not assume a
successful energy shift, spectral gap, absent intervening spectrum or small projection loss.

Both directed spectral comparisons reuse the existing finite-window perturbation theorem.
The lower endpoints are e−h and mu−h, where h>0. Thus the exact count is
ceil((eta+h)/(2h)), even at eta=0. The forward target cutoff is mu+eta+xiB+w; the reverse
target is e+eta+w. The actual energy comparison makes each separation at least w>0.
The displayed losses are the count times (xi+h)^2/(w+h)^2; no smallness is claimed
without subsequent numerical parameter bounds. The matrix lower bounds supply the lower
eigenvalue hypotheses inside the proof.

This is a corrected auxiliary to ALVV, arXiv:1602.08828v2, `lem:exp-approx` and
`t:aisefficient`, lines 1195–1255 and 1373–1392. It does not complete the physical GEN
construction, its source-sharp parameter choices or a running-time theorem.
