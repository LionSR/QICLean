# The two merge deficits on their common copy space

For m copies, let the paired coordinate spaces be Q^m × C^m and V^m × R^m,
using the same enumeration in all four factors. The actual separate and
simultaneous copy actions define D_C = F_Q + F_C − F_QC and
D_R = F_V + F_R − F_VR. Each is Hermitian. Their extensions to the common
space are D_C ⊗ I and I ⊗ D_R, which commute because they act on distinct
factors. For all real a and b,

exp(a(D_C ⊗ I) + b(I ⊗ D_R)) = exp(a D_C) ⊗ exp(b D_R).

For every matrix ρ on the common space, the individual exponential
traces equal the local trace pairings against its actual partial traces.
No positivity, normalization or permutation invariance of ρ is assumed.
The equalities are complex equalities, and therefore give the real trace
pairings used in moment estimates. Zero copies and empty finite coordinate
sets are included.

The source is OpenAI, *A two-dimensional area law from a global spectral
gap*, September 24, 2026, 07-comparators.tex, lines 501–555, equations
(comparator:merge-decomposition) and (comparator:merge-moments), at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. The local deficit uses the actual
PairCopy actions. The exponential and partial-trace proofs reuse the
existing generic tensor-exponential and trace-pairing identities.

The operator factorization does not imply that a joint trace factors
into two marginal traces: correlations in ρ remain. Identification with
the actual good-copy component and its two reduced densities is a separate
argument, as is the weighted estimate combining the two moments.
The complete metric comparator and area-law Theorem 1.1 remain unfinished.

Positivity of each deficit can be obtained in a later step from the
compatible dimension inequality d_ν ≤ d_λ d_μ on every nonzero joint
central block, followed by positivity of the corresponding orthogonal
resolution with coefficients log d_λ + log d_μ − log d_ν. This module
proves the stated operator identities and Hermiticity; it does not yet
include that positivity theorem.
