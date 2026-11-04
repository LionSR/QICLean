# Least viable dimensions and finite dyadic counts

Four auxiliary results support the low-density dimension argument of
Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128.

For a fixed nonnegative viability error, the natural dimensions of viable
regional subspaces have an attained least element. The whole regional
space supplies a member of this set. Restricting the target preserves
viability, so increasing targets have nondecreasing least dimensions.
The result selects actual minimizing subspaces; it does not take an
infimum or require a compactness argument.

For the actual ceiling
`ell = ceil(C * (1 + log m + log(1/g))² / g)` and count
`D = (m * ell²)^(22 * ell)`, with
`g = min(v / (6 * 2^j), 1)`, every prescribed finite natural dimension
is exceeded at some finite dyadic index. The proof uses the explicit
index `j = ceil(N * v / (6 * C))`, rather than a termination premise.
The count and ceiling are unchanged from the improving-family parameters.

The statements are generic auxiliary results. They do not establish the
physical low-density dimension bound, its strict sampling contradiction,
an entropy theorem, an MPS approximation or a running-time bound. Those
require the actual improving family, the calibrated sample, and their
physical hypotheses to be assembled separately.
