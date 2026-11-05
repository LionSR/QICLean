# Positive regional energy after orthogonal projection

A positive regional operator need not annihilate a global ground vector. The projected zero-energy trial-space theorem therefore does not by itself justify the regional energy estimate in the ALVV algorithm.

The new estimate applies to the actual image `P_U G`. If the positive operator has norm at most `A`, its quadratic form is at most `E0` on unit vectors of `G`, and `U` is delta-close to `G`, then its energy on the image is bounded by `[(1+1/t)E0+(1+t)A delta]/(1-delta)` for every positive weight `t`. Taking `E0=2`, `t=8` and `delta<=1/[100(A+1)]` gives the constant three.

The proof uses positivity at `x-t y`, the actual orthogonal projection, Pythagoras and the operator norm.

These are auxiliaries for Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631–1632, and the proof of `t:alg1`, lines 1805–1806. The physical regional quadratic-form bound and the compressed local minimum must still be derived before these estimates establish an energy-estimation invariant. No full algorithm, source iteration count or running time is claimed.
