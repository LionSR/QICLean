# Shared estimates for a corrected soft-truncation approximation

Four modules provide the finite algebra and normalized estimates for a
one-interval soft-truncation approximation. They are auxiliary to ALVV,
arXiv:1602.08828v2, `thm:cluster-approx` and `lem:exp-approx-eff`.

The mandatory-label estimate assumes Hermiticity, local norms at most one,
and an explicit lower energy H >= lambda I. It bounds the finite alternating
sum R by exp(t lambda) ||R|| <= (exp(t) - 1)^|S|. The separate union coefficient
estimate supplies the factor 2^|U| used by the corrected label expansion.
Neither result states the false printed physical-support approximation.
Its counterexamples remain recorded in the published TNLean cluster note.

The finite heat identity retains the constant term and the scale:

    h_(m,t)(U) = sum_(a=0)^m c_a(t,m) exp(-a U/t),
    sum_(a=0)^m |c_a(t,m)| <= t 2^(m+1).

It is proved for the same Hermitian matrix U by continuous functional calculus.
The logarithmic order lemma bounds W (exp(N^2 b^r) - 1) at a requested accuracy.
These estimates do not assert the unrestricted parameter or running-time claim
of the source's approximation lemma.
