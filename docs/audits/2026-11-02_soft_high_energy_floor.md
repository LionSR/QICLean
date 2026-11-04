# A quantitative high-energy floor for the actual soft function

The contribution derives a scalar high-energy floor from the existing
polynomial remainder at a threshold and the actual finite-series monotonicity.
For every positive scale, order at least one and nonnegative threshold R,
the soft function above R is at least R minus its polynomial error at R.
The companion matrix result derives the corresponding lower bound by the
original high-energy projection for the actual function of A-eI, assuming
only that A is Hermitian and A>=eI. No commutativity, projection comparison,
reverse residual or spectral gap is supplied.

A shared functional-calculus translation theorem handles arbitrary functions
on the finite translated spectrum.

The quantitative margin is chosen for fixed order and growing energy width.
For eta>=0, m>=2 and t>=U=2(eta+8), the actual polynomial error at U is at
most U/m and hence U/2. Thus the floor b is at least eta+8. Given an energy
upper bound E<=2 and a boundary count c<=2, subtraction leaves
b-(E+eta)-2c>=2. These energy and count bounds are explicit inputs to the
scalar auxiliary. A physical application must derive them for its actual
soft Hamiltonian and actual boundary set before using this conclusion.

An absolute unit-error condition at eta+8 would instead require a
superlinear scale in the width at fixed order. The relative half-threshold
bound avoids that unnecessary restriction. The independent scale and order
are retained. No full GEN parameter or running-time conclusion is inferred.

The underlying reverse hard-truncation argument can be reused with distinct
barrier and projection thresholds: substitute r=c-b and u=b into the existing
weighted restriction theorem. Its projection/weight threshold is then c and
its denominator is b-energy-2*boundary_count. The actual physical energy,
cardinality, commutation, projection order and subsequent tail-factor
composition remain to be constructed. This contribution is a prerequisite,
not a completed physical reverse theorem. The false printed uniform energy
and cluster estimates are not asserted or restored.

The results support ALVV, arXiv:1602.08828v2, Definitions `def:hard-trunc`,
`def:soft-trunc` and `lem:exp-approx`, lines 873–886, 1178–1185 and
1195–1255.
