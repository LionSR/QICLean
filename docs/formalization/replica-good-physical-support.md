# Actual good physical-copy symmetric support

The physical space of the manuscript is Q tensor Y tensor V, with an independent
middle factor Y. The theorem retains the full physical good-copy space until
symmetrization; it does not use the common QC/VR density, which has already
traced every Y coordinate.

For a unit one-copy vector Ω, an arbitrary original vector u and an excited
subset B, take the actual component w = (R_B tensor I)u. Trace only the bad
physical copies, keeping every auxiliary coordinate. The resulting literal
density is fixed by the physical symmetrizer tensored with the auxiliary
identity. The proof transports the existing product-density identity through
the chosen good-copy enumeration and proves copy invariance of Ω to the mth
tensor power by reordering its finite product.

The single declaration is
`Matrix.symProj_mul_replicaExcitationComponent_goodAuxiliary_density`.
It introduces no new marginal definition, no supplied product equation and no
symmetry or support assumption on u. Zero components, zero copies and empty
good sets are included. The generic finite physical coordinate set A
specializes directly to Q × (Y × V).

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 23 and 103–110 for the independent physical
factors; lines 513–517 for physical symmetric support; lines 520–549 for the
actual product-density step. This result does not assert that merged-region
measurements preserve the physical symmetric subspace. The compatible
spectral projection and its commutation with the deficits are separate steps.
