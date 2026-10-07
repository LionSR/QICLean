# Tactic pattern ledger

Record repeated proof patterns before introducing a new tactic. Prefer an
existing theorem, then a reusable lemma or simp set; promote a new abstraction
only after at least three genuine occurrences across two files. Occurrences
in a regression file are not additional mathematical consumers.

## Promoted

No new tactic or automation is introduced for shifted spectral truncation.
The proofs reuse existing functional-calculus identities, projection
rank/trace comparison, range-of-composition, and scalar real-power bounds.

## Candidates

### Commutation with a matrix inverse — candidate (2026-10-07)

- **Pattern:** Give a positive definite matrix its existing `Invertible`
  instance, use `Commute.invOf_right` or `commute_invOf`, and rewrite
  `Matrix.invOf_eq_nonsing_inv`.
- **Seen:** Three inverse-commutation steps in
  `QICLean/Analysis/PatchRegulator.lean`; one file.
- **Abstraction:** The existing Mathlib commutation lemmas suffice. Retain
  this record until independent occurrences in another file justify a
  matrix-specific lemma; no new tactic is introduced.

### Finite-spectrum functional-calculus scalar reduction — candidate (2026-10-07)

- **Pattern:** Rewrite matrices as Hermitian functional calculi, combine
  products with `← hA.cfc_mul`, and reduce the equality to a pointwise
  threshold split followed by scalar simplification.
- **Seen:** In `QICLean/Analysis/ShiftedDensityTruncation.lean`,
  `IsHermitian.isStarProjection_spectralProjectionGE`,
  `PosSemidef.commute_add_smul_one_rpow_spectralProjectionGE`,
  `PosSemidef.shiftedPowerHead_eq_cfc`, and
  `PosSemidef.shiftedPowerHead_mul_shiftedPowerTail` are representative
  occurrences. In `QICLean/Analysis/SpectralCutoffMass.lean`,
  `PosSemidef.smul_one_sub_spectralCutoff_le` uses the corresponding
  pointwise order reduction; `PosSemidef.spectralCutoff_mass_ge` then takes
  its quadratic form. Their scalar conclusions differ.
- **Abstraction:** Continue using the existing `Matrix.IsHermitian.cfc_mul`
  and `cfc_congr` results for identities, and the generic `cfc_le_iff`
  result for order. The local `hcont` in the cutoff proof supplies
  continuity on the finite spectrum for each scalar function without
  repeating the same continuity argument. These existing mechanisms
  already provide the scalar reduction; no new tactic is introduced.
- **Caveats:** Continuity is required only on the finite spectrum. Do not
  claim global continuity of a threshold indicator. Nonnegativity and
  norm estimates still require the correct PSD and exponent hypotheses.

### Reverse range inclusion from a commuting inverse — candidate (2026-10-07)

- **Pattern:** Prove both range inclusions from H = ΠF and Π = HF⁻¹, using
  `LinearMap.range_comp_le_range` after translating matrix products.
- **Seen:** The two inclusions in
  `Matrix.PosSemidef.range_shiftedPowerHead`; one mathematical consumer
  in one file.
- **Abstraction:** Keep the existing range-of-composition theorem. The
  public range equality is the reusable mathematical result; introducing
  another tactic would not remove independent repeated work.
- **Caveats:** Commutation and the actual inverse identity are proved before
  use. Neither an abstract range certificate nor invertibility of the
  unshifted PSD matrix is assumed.

### Norm of a finite product of vectors — candidate (2026-10-07)

- **Pattern:** Reduce normalization to a one-coordinate sum, then apply
  `Fintype.prod_sum` to the literal finite product. For complex pairings,
  distribute the product over multiplication; for squared norms, use
  `norm_prod` and `Finset.prod_pow`.
- **Seen:** The contraction recovery and norm equality in
  `QICLean/Analysis/ReplicaGoodCopyFactorization.lean`; one file.
- **Abstraction:** Existing finite sum and product identities suffice. No
  new public tensor-vector definition or automation is introduced.
- **Caveats:** Retain the canonical coordinate equivalence and every
  auxiliary coordinate. Empty products have value one.

### Finite-product partial traces — candidate (2026-10-08)

- **Pattern:** Reindex a partial trace by the existing finite-product splitting equivalence, insert the proved coordinate factorization, and factor the resulting finite sums.
- **Seen:** Ground-copy contraction and norm preservation in `Analysis/ReplicaGoodCopyFactorization.lean`, and marginal identification in `Analysis/ReplicaGoodCopyDensity.lean`.
- **Abstraction:** The existing `FiniteProduct.splitEquiv`, `Fintype.prod_sum`, and finite-sum multiplication lemmas supply the reindexing and product calculation. The new public density identities carry these calculations to later consumers; no new tactic is introduced.
- **Caveat:** Normalization belongs only to the prescribed ground vector. The excitation component and its auxiliary marginal may have zero or arbitrary total mass.
