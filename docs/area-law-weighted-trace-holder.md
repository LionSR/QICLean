# Weighted exponential trace inequalities

The sharp component estimate in Section 7 of the September 24, 2026 area-law
manuscript uses Hölder's inequality for five commuting Hermitian operators.
The finite-dimensional trace inequalities established here provide that
analytic step. The weight is any positive semidefinite matrix, with no
normalization or commutation condition.

For commuting Hermitian matrices A and B and a weight \(\rho\ge0\),
\[
\operatorname{ReTr}(\rho e^{tA+(1-t)B})
\le [\operatorname{ReTr}(\rho e^A)]^t
    [\operatorname{ReTr}(\rho e^B)]^{1-t},\qquad 0\le t\le1.
\]
For a nonempty family of r pairwise commuting Hermitian matrices and any real a,
\[
\operatorname{ReTr}\!\left(\rho e^{a\sum_j A_j}\right)
\le\prod_j[\operatorname{ReTr}(\rho e^{raA_j})]^{1/r}.
\]
Every exponential trace appearing here is nonnegative. Zero weights, endpoint
weights and empty ambient coordinate sets are included. The number of factors
is positive; the five-factor specialization uses r=5.

The proof forms the actual joint spectral projections of A and B and applies
scalar weighted Hölder to their nonnegative trace weights. The scalar proof
uses convexity of the exponential after dividing by the positive individual
moments; the all-zero weight is treated separately. Induction gives the
finite-family inequality. No simultaneous eigenbasis or spectral certificate
is supplied as a hypothesis.

Source: [Section 7, lines 553–560](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/07-comparators.tex#L553-L560).
The actual five physical factors, their commutations, signed centered label
rates and application to the excitation density require separate proofs.
These auxiliary inequalities alone do not establish the sharp comparator or
the ground-state area law.
