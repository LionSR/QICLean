# The compatible physical-label projection

The [compatible-label argument in Section 7](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/07-comparators.tex#L501-L522)
uses five independent factors \(Q,Y,V,C,R\). The physical operator is
\(G_{\mathrm{phys}}=F_Q+F_V-F_Y\). Here \(Y\) is a third physical region;
its label observable can agree with that of \(QV\) only on the physical
symmetric subspace.

The module uses the actual copy actions on configurations with five factors,
in the order \(Q=0,Y=1,V=2,C=3,R=4\). Let \(P\) average the simultaneous
copy permutations of \(Q,Y,V\), leaving the auxiliary factors fixed.
Complementary central coefficients give \(F_YP=F_{QV}P\). Nesting gives
commutation of \(P\) with \(F_Q,F_V,F_{QV}\), hence
\[
G_{\mathrm{phys}}P=P(F_Q+F_V-F_{QV}).
\]
The actual \(QV\) merge deficit is nonnegative. The verified spectral
intertwining theorem therefore gives
\(\mathbf1_{[0,\infty)}(G_{\mathrm{phys}})P=P\), including the zero
eigenvalues, zero copies and empty finite factors.

Every real function of \(G_{\mathrm{phys}}\) commutes with the actual
\(QC\) and \(VR\) real label observables, the individual \(C\) and \(R\)
auxiliary label observables, and the two actual merge
deficits. All singleton and merged-label commutations are derived from
nesting and disjointness of the five specified factors. No density,
normalization, invariance or compatibility certificate is a premise.
In particular, these identities justify retaining the nonnegative
physical spectral projection while the two merge deficits are measured.
They make no assertion that a merge preserves the whole physical
symmetric subspace, or that \(G_{\mathrm{phys}}\) is nonnegative globally.

The actual excitation density and its symmetric support are separate
results. Applying these identities to that density in physical-plus-auxiliary
coordinates also requires the canonical pointwise regrouping of the five
factors. This module supplies the operator step; the exponential moment
estimates, inverse-compression estimate and ground-state area law remain
separate mathematical obligations.
