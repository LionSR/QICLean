# Regional information decreases under discarding

For a finite-product pure vector ψ, regional entropy is the von Neumann entropy
of the actual reduction of |ψ⟩⟨ψ|. The following statements are proved in
`QICLean/Entropy/FiniteProductInformation.lean`:

- Conditional mutual information I(X:C | Z) is nonnegative when X,C,Z are
  pairwise disjoint.
- Regional entropy is submodular:
  S(R ∪ T) + S(R ∩ T) ≤ S(R) + S(T), with no disjointness restriction on R,T.
- If R ⊆ T and T is disjoint from J, then I(R:J) ≤ I(T:J).

These are actual reduced-state entropy inequalities, without an assumed entropy
inequality or Hamiltonian premise. Their balanced expressions remain valid for
unnormalized vectors; the proof uses the existing strong-subadditivity theorem
for arbitrary positive matrices. This extension does not assert nonnegativity of
ordinary mutual information for an unnormalized vector.

The mathematical source is the finite-dimensional entropy discussion in
[Section 2 of OpenAI's area-law manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/01-preliminaries.tex#L19),
September 24, 2026. Information monotonicity supplies exactly the final
[subset step of the amplification proof](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/09-amplification.tex#L560).
Both citations refer to commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The proof expresses the actual XZC reduction in the product basis
E_X × (E_Z × E_C). Existing regional reduction-composition results identify
its XZ, ZC and Z marginals. Canonical coordinate associativity and entropy
invariance under finite reindexing reduce the statement to positive-matrix
strong subadditivity. Applying this argument to R \ T, R ∩ T, T \ R gives
submodularity. Applying submodularity to R ∪ J and T proves information
monotonicity.

All new proof text is original. No upstream Lean proof text is copied or
adapted; the imported QICLean results retain their existing attribution.
OpenAI Codex assisted with the proof, mathematical source comparison,
documentation and verification. Human mathematical review remains separate.
The global area law and the amplification proposition require further results;
this contribution establishes their finite-region entropy consequences.
