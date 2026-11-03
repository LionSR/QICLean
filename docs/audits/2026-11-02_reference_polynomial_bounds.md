# Power bounds from the reference bond logarithm

The scalar factor b^(3/4)(1 + log b) is at most 5b for b ≥ 1.
Consequently a reference estimate of the form

    log B ≤ K (a0 + a1 b^(3/4))(1 + log b)

with nonnegative coefficients is at most K(a0 + 5a1)b. When
b = b0 + log X, exponentiation bounds B by exp(p b0) X^p,
where p = K(a0 + 5a1). The proofs reuse Mathlib logarithm and
real-power inequalities.

These numerical estimates simplify the reference bounds in the actual
common-threshold tree construction. They do not by themselves assert
a polynomial bond bound for that complete construction: the physical
norm and accuracy parameters and the remaining scalar counts still
have to be substituted. No algorithmic running time is claimed.

The inverse final parameters also have exact expressions. For x=A/gamma
and y=1/eta, the common-radius cost is 1/(c rho)=2x^2 y+x, at most
3(1+x)^2(1+y). The reference cost is 1/epsilon=65536x^3 y+32768x^2,
at most 98304(1+x)^3(1+y). These estimates will allow substitution of
the physical norm bound into the dimension and bond counts without
hiding an inverse-accuracy dependence in a chosen constant.
