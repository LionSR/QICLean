# Actual filtering and reference-space collective trimming

The new one-step theorem combines the literal linear image under K with
the literal collective trimming projections. The filtered span S is required
to contain K(U tensor H_B); its image inclusion is an explicit construction
obligation. The reference space R approximates the target T in both directions
and has a uniform Schmidt-rank bound b across the m actual cuts.

For squared-norm contraction 1−c with 0<c≤1, choose robustness weight c/16.
Reference error ε≤c²η/1024 and threshold ξ>0 satisfying ξ√(mb)≤cη/48 yield

    δ_next ≤ (1−c/4)δ+cη/8,      0≤δ≤1/2.

A new Mathlib-only numerical lemma bounds these exact constants. The result
uses the corrected collective-trimming increment 2ξ√(mb) documented in
`docs/paper-gaps/alvv16_trimming_constant.tex`. It implements the local
reference argument of ALVV, arXiv:1602.08828v2, proof of Theorem t:alg1,
lines 1801–1813. It places no requirement that the entire filtered image
remain close to the entire untrimmed space after trimming.

The physical reference with this chosen accuracy, the repeated actual
subspace construction, its dimension and MPS bounds, and the final r-dimensional
compressed spectral subspace remain separate steps. No completion of the full
source algorithm is asserted by this auxiliary.
