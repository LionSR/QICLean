# Exponential merge moments of excitation components

Let Ω be a unit vector on Q ⊗ T, and let u be a vector on
(Q ⊗ T)^{⊗k} ⊗ C^{⊗k} ⊗ D^{⊗k}, invariant under simultaneous permutation
of the three copy strings. For a set B of bad copies, put m = |Bᶜ| and
w = (R_B ⊗ I)u. Retain the good Q and C coordinates of this same component
and trace every other coordinate. Denote the resulting positive matrix by ρ.
For the actual Schur-label observables of the separate Q and C actions and
their simultaneous product, put D_C = F_Q + F_C − F_QC. Then

Re Tr(ρ exp(b D_C)) ≤ (m + 1)^((dim Q · dim C)^2) ‖w‖²

for every real b ≤ 1. The component may be unnormalized or zero; zero
copies and an empty set of good copies are included.

The source is OpenAI, *A two-dimensional area law from a global spectral
gap*, September 24, 2026, Section 7, equation (comparator:merge-moments),
07-comparators.tex, lines 520–549, at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. The source's range 0 ≤ b ≤ 1 is
included. Its normalized expectation follows by dividing by ‖w‖² when w
is nonzero. Interchanging the physical and auxiliary factors gives the
corresponding local estimate for the other merge deficit.

The literal joint density factors as the tensor power of the original
one-copy Q marginal times the actual good C marginal. The physical factor
commutes with every copy permutation. Permutation invariance of the
auxiliary factor follows from the original simultaneous symmetry, rather
than an additional assumption about its density. These identities give
both separate invariances required by the homogeneous paired moment
estimate. The exponential trace expansion identifies its finite-label
moment with the left side above. Trace preservation and ‖Ω‖ = 1 give the
mass ‖w‖² on the right side.

This proves the component merge moment with the original symmetry
hypothesis. It does not yet prove the inverse-compression estimate or the
comparison of complete buffered-rectangle metrics. Combining the two
local moments requires the actual coordinate identifications and the
commutation of the corresponding operators on their common space. The
area-law Theorem 1.1 remains unfinished.
