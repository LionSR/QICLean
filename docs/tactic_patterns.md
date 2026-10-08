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

### Unit-blank contraction in restoration — promoted lemmas (2026-10-08)

- **Pattern:** Expand restoring matrix entries and contract unit ancillary
  blanks through `∑ i, star (b i) * b i = 1`.
- **Seen:** The copied-vector identity in `RestoringVectors.lean` and the actual
  ground-component coefficient proof in `RestoringGroundComponent.lean`.
- **Abstraction:** Promote the already proved blank normalization and restoring
  entry formula as `restoringBlank_sum_eq_one` and
  `restoringOperatorWithAncilla_apply`, preserving their existing proof bodies.
  The new coefficient proof reuses both instead of duplicating those expansions.
- **Caveats:** Blank norms are Euclidean. The copied ancillary coordinate runs
  over the whole basis, including coordinates with zero assigned probability.

## Candidates

### Orthogonal projection mass from the actual marginal — candidate (2026-10-07)

- **Pattern:** Use the partial-trace pairing, cyclicity of trace and the pure
  matrix trace to express a projected mass as a sesquilinear pairing. Move
  the projector across that pairing, then use idempotence, self-adjointness
  and the Euclidean norm identity.
- **Seen:** The private `norm_sq_mulVec_eq_re_trace` calculation in
  `QICLean/Entropy/PureTensorPower.lean`, and the local `hmass` calculation
  in `TensorPower.exists_labelProj_norm_mass_ge` on the separate
  `SchurSectorMass` contribution. These are two mathematical consumers.
- **Abstraction:** The actual product marginal and projected-mass identities
  are the public conclusions here. Keep the general pairing calculation
  private while the two contributions remain independent; reconsider a
  shared lemma when a third mathematical consumer occurs.
- **Caveats:** Orthogonality is proved for the actual projector. Neither the
  desired projected mass nor a supplied reduced-density identity is assumed.

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

### Actual copy-coordinate regrouping before a partial trace — candidate (2026-10-08)

- **Pattern:** Construct the good/bad coordinate equivalence, derive its actual
  permutation action, reindex the literal product operator and transport a
  fixed-vector equation before applying partial-trace covariance.
- **Seen:** The chosen complement/subset split appears in
  `Analysis/ReplicaGoodAuxiliaryLabelBound.lean` and
  `Analysis/ReplicaGoodAuxiliaryMarginal.lean` (two files). The latter also
  reuses the configuration and matrix-entry calculations in its marginal
  theorem.
- **Abstraction:** The public good/bad configuration equivalence is the common
  mathematical construction for subsequent consumers. The earlier frozen
  label-bound source remains unchanged; new consumers should reuse this
  public construction rather than add a third private split. Existing
  reindexing and marginal-symmetry theorems supply the action and trace
  steps; no new tactic is required.
- **Caveat:** A compatible regrouped action or an invariant marginal must be
  derived. It must not be introduced as a supplied certificate. Chosen
  finite-set equivalences need not enumerate the copies in increasing order.

### Sector mass from a finite resolution — candidate (2026-10-07)

- **Pattern:** Restrict trace masses to the nonzero projections, use positivity
  and completeness to obtain a nonempty set of total mass one, and apply
  `Finset.exists_le_of_sum_le` with a bound on the number of projections.
- **Seen:** `TensorPower.exists_labelProj_trace_mass_ge` in
  `QICLean/Representation/SchurSectorMass.lean`; one mathematical consumer.
- **Abstraction:** Reuse the existing finite-sum comparison theorem. The
  projected-vector result applies this trace result to the actual reduced
  state and uses the trace-pairing and Hermitian-idempotent norm identities.
  No new tactic is needed.
- **Caveats:** The sector count gives a mass bound only; an entropy window
  requires a separate concentration estimate and a restricted selection.

### Joint spectral trace reduction — candidate (2026-10-07)

- **Pattern:** Express the density and the tested observable through the
  joint orthogonal resolution, multiply using its algebra homomorphism, and
  take the trace as a finite weighted sum.
- **Seen:** The surprisal tail, label-window mass and exponential remainder
  in `QICLean/Representation/HighLabelWindow.lean` use the private
  `re_trace_mul_joint_hom` lemma; the existing moment calculation in
  `SchurSurprisal.lean` has the corresponding finite trace expansion.
- **Abstraction:** A single private mathematical lemma handles all three
  new uses. The existing resolution homomorphism and trace theorem remain
  the common public results; no tactic is introduced.
- **Caveats:** The density is positive semidefinite and permutation invariant.
  Zero eigenvalues contribute zero mass. A trace expansion must not be
  substituted for either concentration or the moment bound itself.

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

### Regional finite-product marginal — candidate (2026-10-08)

- **Pattern:** Use the chosen finite-set enumeration to convert a good-copy product to a finite Kronecker power, and apply `Fintype.prod_sum` after tracing one physical coordinate per copy.
- **Seen:** `Analysis/ReplicaRegionalDensity.lean`; the auxiliary marginal calculation in `Analysis/ReplicaGoodCopyDensity.lean` uses the same existing finite-product identities.
- **Abstraction:** Existing `Equiv.prod_comp`, `Fintype.prod_sum` and finite-sum multiplication lemmas perform the calculation. The new regional density theorem carries it to the physical consumer; no new tactic is introduced.
- **Caveat:** Keep the literal excitation component and its own auxiliary density. Only the prescribed one-copy ground vector is normalized.

### Contraction of the repeated uniform pair — candidate (2026-10-07)

- **Pattern:** Expand a Kronecker action against the actual repeated uniform
  pair, rewrite its coordinates as a scalar times the equality indicator,
  and contract one coordinate sum.
- **Seen:** The two private coordinate identities in
  `QICLean/Representation/UniformBellLabel.lean`; two occurrences in one file.
- **Abstraction:** The public projected-norm and nonzero-occurrence theorems
  supply the mathematical consequences. A separate tactic is not warranted
  by two coordinate contractions.
- **Caveats:** The normalization depends on the actual one-copy dimension;
  nonzero occurrence requires that dimension to be positive. The central
  Schur label equality additionally uses inversion-invariant coefficients.

### Tensor-product actions in product coordinates — candidate (2026-10-08)

- **Pattern:** Expand a Kronecker action on a product vector and apply the
  distributive law for two finite sums. Factor the physical and auxiliary
  actions before using their individual fixed-vector equations.
- **Seen:** The two auxiliary-label equations and simultaneous symmetry in
  `QICLean/Representation/ReplicaPrevector.lean` share the private generic
  `kronecker_mulVec_product` lemma. The mean-energy calculation in
  `QICLean/Analysis/ReplicaDefect.lean` has a prior identity-spectator variant.
- **Abstraction:** The new calculation is written once and reused for all
  three actions. The norm calculation reuses the existing public quadratic
  form factorization. Reconsider a common algebraic action lemma when a
  further independent consumer needs it; no tactic is introduced here.
- **Caveats:** The actual matrix actions and vector factors are used. No
  supplied factorization or eigenvector statement for the initial vector
  replaces these calculations.

### Projection after regrouping tensor factors — candidate (2026-10-08)

- **Pattern:** Keep the physical coefficient fixed while an operator acts
  on the selected auxiliary factor, and identify the result after regrouping
  the physical and auxiliary coordinates.
- **Seen:** `QICLean/Representation/SchmidtBellPrevector.lean` has one new
  consumer. The earlier product-action and identity-spectator calculations
  occur in `ReplicaPrevector.lean` and `ReplicaDefect.lean`.
- **Abstraction:** The new calculation reuses Mathlib's
  `Matrix.vec_mul_eq_mulVec` twice. A single private lemma applies this
  matrix-vectorization identity to the two coordinate maps, and the public
  result combines it with the existing finite-copy Bell identity. The
  reindexing of that identity uses `Matrix.submatrix_mulVec_equiv`.
- **Caveats:** The right auxiliary projector remains on its actual selected
  copy space. The Bell projection acts on the physical and left auxiliary
  factors; the asserted label of the projected output is the right label.
