# Scalar ceiling and dyadic count estimates

This note concerns the two scalar modules `PolynomialFilterCeil` and
`PolynomialFilterCounts`.

For A≥100 and a fixed natural m with log m≥100, put

    u_g = 1 + log m + log(1/g),
    ell_g = ceil(A*u_g²/g),
    D_g = (m*ell_g²)^(22*ell_g).

If 0<g,h≤1 and g≤2h, the actual natural ceilings satisfy
ell_h≤(21/10)ell_g, and the actual counts satisfy

    100 ≤ log D_g,       log D_h ≤ (13/6)log D_g.

Integer rounding is included. The scalar modules assume no physical filter,
count estimate or suppression bound, and prove no low-density dimension or
sampling theorem.
The source context is ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. The explicit finite thresholds
belong to these supporting numerical statements.
