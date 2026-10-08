# Merge deficits and the nonnegative physical spectral projection

The area-law manuscript defines the two actual deficits
\(D_C=F_Q+F_C-F_{QC}\) and \(D_R=F_V+F_R-F_{VR}\).
Its [merge-dimension inequality](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/05-replicas.tex#L102-L106)
implies positivity of both deficits on their entire actual paired copy spaces.
The formal result is stated for arbitrary commuting finite-group permutation
actions and their pointwise product, then specialized to the literal paired
copy actions. No compatibility premise is supplied: it is derived only for
the nonzero joint central projections. Empty ambient spaces and zero copies
are included.

The same contribution proves two auxiliary spectral facts. The closed
nonnegative spectral projection of a positive matrix is the identity,
including its kernel. If a Hermitian matrix A and a positive matrix B satisfy
AT=TB for a rectangular matrix T, then the nonnegative spectral projection of
A fixes every vector in the range of T. This follows from the existing
Hermitian functional-calculus intertwining theorem. T need not be an
isometry or projection, and its range may vanish.

The physical quantity in the [compatible-label argument](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/07-comparators.tex#L501-L522)
is \(G_{\mathrm{phys}}=F_Q+F_V-F_Y\), where Q, Y and V are independent
physical regions. Its middle term cannot be identified globally with the
combined QV action. A physical application must derive the complementary
label identity on the actual physical symmetric projection and then derive
the appropriate intertwining relation. These identities and commutation of
the compatible physical projection with the merged labels are separate work.
No invariance of the entire physical symmetric subspace under a merge is
asserted here.

The original exponential-resolution and common-space deficit declarations
remain unchanged. The contribution adds positivity after them and reuses
existing spectral calculus. It does not establish the complete
inverse-compression estimate or the headline ground-state area law.
