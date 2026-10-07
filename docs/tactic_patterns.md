# Tactic pattern ledger

Record repeated proof patterns before introducing a new tactic. Prefer an
existing theorem, then a reusable lemma or simp set; promote a new abstraction
only after at least three genuine occurrences across two files. Occurrences
in a regression file are not additional mathematical consumers.

## Promoted

No new tactic or automation is introduced for shifted spectral truncation.
The proofs reuse existing functional-calculus identities, projection
rank/trace comparison, range-of-composition, and scalar real-power bounds.

### Joint central-label resolution — existing mathematical lemmas (2026-10-07)

- **Pattern:** Form the product of commuting orthogonal resolutions, express
  the observables as functions of this joint resolution, and prove matrix
  order from scalar inequalities on its nonzero components.
- **Seen:** `TensorPower.copyPerm_groupedCopies_labelEntropy_bounds` in
  `QICLean/Representation/GoodAuxiliaryLabelEntropy.lean`, as well as `TensorPower.groupedCopies_labelEntropy_bounds` in
  `QICLean/Representation/GroupedLabelEntropy.lean` and
  `PermutationRepresentation.supportProj_mul_labelEntropy_mul_supportProj_le`
  in `QICLean/Representation/SchurSurprisal.lean`.
- **Abstraction:** Reuse `Matrix.IsOrthogonalResolution.prod` and
  `posSemidef_hom_of_ne_zero`. The coordinate functions of a product
  resolution are recovered by summing the other factor to the identity;
  the new module has two private lemmas for this elementary calculation.
- **Caveats:** Scalar inequalities are required only on nonzero joint
  projections. Compatibility and the full-space order must be derived from
  the actual projections, rather than supplied as extra assumptions.


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

### Spectator coordinates in a central projection — candidate (2026-10-07)

- **Pattern:** Prove the actual permutation entry condition in split coordinates,
  then expand the group-algebra sum to identify the central projection entry
  as an identity on the fixed coordinates times the projection on the moving
  coordinates. Nonvanishing on the whole space forces nonvanishing on the
  moving coordinates.
- **Seen:** The private entry proof in
  `QICLean/Representation/BadCopyLabelDimension.lean`; one mathematical
  consumer in one file.
- **Abstraction:** Reuse the existing permutation-entry and group-algebra
  formulas. The ensuing dimension estimate uses the existing
  `dim_le_finrank_of_invariant` theorem; no new tactic or competing general
  representation definition is introduced.
- **Caveats:** The actual group action and specified coordinate split are
  essential. Fixed-coordinate multiplicity must not be included in the
  dimension of the moving tensor power. Empty coordinate sets and zero
  moving coordinates remain included.

### Compression by an actual central projection — candidate (2026-10-08)

- **Pattern:** Apply `PosSemidef.conjTranspose_mul_mul_same` to a derived
  matrix order inequality, then use Hermiticity, idempotence and the
  actual central-observable eigenvalue identity to simplify the result.
- **Seen:** `TensorPower.copyPerm_groupedGood_labelEntropy_compression` in
  `QICLean/Representation/GoodAuxiliaryLabelCompression.lean`; one new
  mathematical consumer. The existing support-compression arguments in
  `SchurSurprisal.lean` also use the same Mathlib conjugation theorem.
- **Abstraction:** Reuse the Mathlib conjugation theorem and the existing
  `labelObservable_mul_labelProj` identity. No new tactic or generic
  projection-compression definition is introduced.
- **Caveats:** The central projection and its eigenvalue are derived from
  the actual representation. Labels with zero projection need no separate
  occurrence assumption; physical excitation support remains a distinct
  assertion.

### Copy-permutation commutation from invariant entries — candidate (2026-10-07)

- **Pattern:** Reindex a literal finite product, or a sum of such products, by
  the inverse copy permutation; convert the resulting simultaneous row and
  column invariance into matrix commutation.
- **Seen:** The replica sum and constant tensor power in
  `QICLean/Analysis/ReplicaPermutationCovariance.lean`; two consumers in one
  file.
- **Abstraction:** The private `commute_copyPerm_of_invariant_entries` shares
  the matrix permutation calculation. The finite reindexing uses existing
  `Fintype.sum_equiv` and `Fintype.prod_equiv`; no new tactic is introduced.
- **Caveats:** Respect the inverse convention of `permOp`. Use the existing
  `Commute.cfc_real` to transfer actual commutation to real functional
  calculus; no continuity or invariance hypothesis on the cutoff is added.

### Permutation covariance of exact sectors — candidate (2026-10-08)

- **Pattern:** Reindex the one-copy product by the inverse permutation, tracking
  the image of its distinguished subset, and reduce matrix multiplication by
  permutation matrices with the existing `PEquiv` multiplication lemmas.
- **Seen:** Exact-sector covariance in `Analysis/ReplicaExcitationSymmetry.lean`;
  invariant-entry reduction in `Analysis/ReplicaPermutationCovariance.lean`.
- **Abstraction:** The existing `PEquiv.toMatrix_toPEquiv_mul` and
  `PEquiv.mul_toMatrix_toPEquiv` perform the matrix calculation in both files.
  The public covariance theorem handles all actual excitation subsets; its
  stabilizer and auxiliary consequences reuse it. No new tactic is needed.
- **Caveat:** The image is σB for the convention x(j)↦x(σ⁻¹j). An individual
  subset projection commutes only with its stabilizer, not arbitrary metrics.

### Disjoint label preservation and a lifted quadratic bound — candidate (2026-10-08)

- **Pattern:** Derive a whole-label fixed-vector equation for a literal
  physical component by the identity-permutation case of excitation
  symmetry. Lift an already derived positive semidefinite compression by
  identities on all spectator registers, then cancel the Hermitian label
  projection on both sides of its quadratic form.
- **Seen:** `Matrix.replicaExcitationComponent_goodAuxiliary_labelEntropy_lower`
  in `QICLean/Analysis/ReplicaGoodAuxiliaryLabelBound.lean`; one mathematical
  consumer.
- **Abstraction:** Reuse `PosSemidef.kronecker`, `kroneckerBilinear`, and
  the actual excitation fixed-vector theorem. The local linear map is the
  literal identity lift, not a new public lifting construction.
- **Caveats:** Only the original vector's label equation is assumed. The
  component's label equation and the good/bad coordinate split are derived.
  Do not replace either with a certificate or commute a physical excitation
  projection through a band metric.
### Marginal invariance from a simultaneous fixed vector — candidate (2026-10-08)

- **Pattern:** Convert a fixed-vector equation into conjugation invariance of
  its rank-one density, apply existing partial-trace covariance, and cancel
  the adjoint of the retained unitary.
- **Seen:** `Analysis/ReplicaMarginalSymmetry.lean`; one mathematical
  calculation and its excitation-component corollary.
- **Abstraction:** The public fixed-vector theorem supplies the common
  partial-trace step. The component corollary reuses it after deriving
  fixedness from the stabilizer theorem. No new tactic is needed.
- **Caveat:** Invariance alone does not imply that different copies are
  independent or establish a merge-moment bound.
