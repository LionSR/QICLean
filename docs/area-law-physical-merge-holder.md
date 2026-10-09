# Five-factor Hölder for the actual merge deficits

Let Q, Y, V, C and R be independent finite-dimensional factors, with m copies
of each. The actual subsystem copy-permutation actions define their central
logarithmic dimension observables F_A. Put
\[
D_C=F_Q+F_C-F_{QC},\qquad D_R=F_V+F_R-F_{VR},\qquad G=F_Q+F_V-F_Y.
\]
The middle region Y is independent of Q and V.

For any positive semidefinite matrix \(\rho\) on the common copy space and any
real a, the formalized inequality is
\[
\operatorname{ReTr}(\rho e^{a(D_C+D_R-G)})
\le
\bigl[\operatorname{ReTr}(\rho e^{5aD_C})\bigr]^{1/5}
\bigl[\operatorname{ReTr}(\rho e^{5aD_R})\bigr]^{1/5}
\bigl[\operatorname{ReTr}(\rho e^{-5aF_Q})\bigr]^{1/5}
\bigl[\operatorname{ReTr}(\rho e^{-5aF_V})\bigr]^{1/5}
\bigl[\operatorname{ReTr}(\rho e^{5aF_Y})\bigr]^{1/5}.
\]
No normalization, invariance or commutation condition is imposed on the trace
weight. All exponential trace moments are actual matrix expressions. The
statement includes zero weights, zero copies and empty factors.

The seven subsystems Q, Y, V, C, R, QC and VR are pairwise nested or disjoint.
The existing central-projector commutation theorems therefore give commutation
of their real label observables. Direct sums, differences and signs then give
all pairwise commutations of the five displayed operators. Equal-weight trace
Hölder applies to this actual family, with no supplied spectral resolution or
commutation certificate.

Source: [Section 7, lines 556–560](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/07-comparators.tex#L556-L560),
with the operators defined at lines 501–506. This proves the analytic Hölder
step. Identification of the trace weight with an excitation density, the signed
physical moment rates, and the final inverse estimate are separate assertions.
Neither global positivity of G nor preservation of the physical symmetric
projection under a merge is a premise or a conclusion here.
