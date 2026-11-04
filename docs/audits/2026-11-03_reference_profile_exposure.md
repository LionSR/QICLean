# Reusing the existing logarithmic reference estimates

Two existing proofs in RefinementOutputPolynomialBound are public:

- Real.reference_accuracy_log_profile_bounds;
- Real.reference_profile_polynomial_bound.

The existing complete-cost theorem continues to use these proofs.

The first estimate turns an inverse-accuracy bound epsilon^(-1)<=K Z^4
into 1<=b<=b0+log(Z^5). The second bounds a monotone logarithmic reference
expression by an explicit constant times a natural power. Future independent
truncation estimates can use Z'=Z^Q to cover larger polynomial accuracy
costs, without repeating either logarithmic argument. Both are numerical
auxiliaries supporting ALVV, arXiv:1602.08828v2, proof of t:alg1,
lines 1801–1817; no new physical construction or runtime bound is asserted.
