# Tactic pattern ledger

Record repeated proof patterns before introducing a new tactic. Prefer an
existing theorem, then a reusable lemma or simp set; promote a new abstraction
only after at least three genuine occurrences across two files. Occurrences
in a regression file are not additional mathematical consumers.

## Promoted

No new tactic or automation is introduced for shifted spectral truncation.
The proofs reuse existing functional-calculus identities, projection
rank/trace comparison, range-of-composition, and scalar real-power bounds.

### Operator norm in orthonormal coordinates — promoted (2026-10-08)

- **Pattern:** Identify the matrix of a continuous linear map in finite
  orthonormal input and output bases, then transfer its operator-norm bound.
- **Result:** `ContinuousLinearMap.norm_toMatrix_orthonormal` in
  `QICLean/Analysis/OrthonormalMatrixNorm.lean` gives equality of norms.
  It reuses Mathlib's Euclidean matrix norm and invariance under composition
  with linear isometric equivalences. Rectangular matrices and empty bases
  require no separate cases.
- **Consumers:** TNLean's `Word.norm_preparedMatrix_le_one`,
  `Word.norm_freeSourceMatrix_le_one`, and the new
  `Word.norm_physicalOutputMatrix_le_one` in `ExteriorSourceContraction`.
- **Decision:** The third application justifies one general equality. The
  prepared TNLean refactor removes the two older coordinate-vector proofs;
  it will be applied together with the dependency update. No custom tactic
  or duplicate coordinate-norm theorem is introduced.

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

### The range of a product of commuting projections — candidate (2026-10-09)

- **Pattern:** Multiply an actual product projection by each of its factors,
  then transfer the resulting matrix identities to every fixed vector.
- **Seen:** `Matrix.replicaLowDefectProjection_fixed_conditions` uses one
  local matrix-to-vector implication for the physical cutoff, auxiliary
  label product, and simultaneous symmetry. The individual auxiliary
  equations then use the same tensor-product multiplication identity.
- **Abstraction:** Reuse `IsStarProjection.mul`, the existing central-label
  commutations, and `symProj_mulVec_mem`. The symmetry average's projection
  properties follow from `exists_labelProj_eq_symProj`; no new averaging
  theorem or tactic is introduced.
- **Caveat:** The derived commutations concern the cutoff, auxiliary labels,
  and symmetry. They do not imply commutation with a replica metric.
### Separate merge moments before Hölder — candidate (2026-10-09)

- **Pattern:** Express an exponential trace on a product space through its
  actual marginal, then preserve the component mass under a coordinate exchange.
- **Seen:** The two estimates formerly local to
  `replicaGoodPairMarginal_exp_sum_mergeDeficit_le` are reused by the separate
  full-density estimate in `ReplicaGoodConfigurationIndividualMergeMoment`.
- **Abstraction:** The public
  `replicaGoodPairMarginal_exp_mergeDeficits_le` contains both separate bounds.
  The arithmetic-mean theorem uses it at twice the parameter; the full-density
  theorem transports each bound by the existing paired-coordinate equivalence.
- **Caveat:** The same actual excitation component occurs throughout, including
  zero mass. No normalized auxiliary marginal or nonvanishing assumption is added.
- **Coordinate simplification:** As in the existing paired exponential transport,
  use `Matrix.submatrix_smul` followed by `Pi.smul_apply` at both coordinate
  arguments. The first equality concerns a function of the two coordinate maps;
  reducing its applications exposes the actual transported matrix. This reuses
  the existing Mathlib statements and needs no new tactic.


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

### Exponential on an actual joint label resolution — candidate (2026-10-08)

- **Pattern:** Construct a joint resolution from commuting actual label projections, identify its marginal observables using the projection sums, and apply `Matrix.IsOrthogonalResolution.exp_hom` before a positive-dimension scalar logarithm calculation.
- **Seen:** `Representation/SchurSurprisal.lean` and `Representation/MergeExponential.lean`; two mathematical exponential calculations in two files.
- **Abstraction:** The existing resolution homomorphism and `exp_hom` already supply the functional-calculus step. Continue using these results and finite-sum identities; no additional tactic or duplicate spectral calculus is introduced.
- **Caveat:** Derive the joint resolution from the actual projections. Positive irreducible dimensions justify the logarithms even when their ambient label projections vanish.

### Covariance under a finite coordinate bijection — candidate (2026-10-08)

- **Pattern:** Transport a density and permutation operators by one basis
  bijection, obtain the central projectors by the group-algebra sum, and
  compare the actual product traces using finite-sum reindexing.
- **Seen:** The three copy actions and joint trace in
  `QICLean/Representation/PairMergeMoment.lean` share one private transport
  calculation. The matrix products reuse `Matrix.submatrix_mul_equiv`.
- **Abstraction:** Keep the common permutation/projector and trace calculations
  as private lemmas. No new tactic is justified by one mathematical module.
- **Caveats:** Use the same coordinate bijection for the density and all three
  actions; separate permutation invariance is a premise of the auxiliary
  theorem and must be proved in its physical application.

### Total normalization of an invariant positive component — candidate (2026-10-08)

- **Pattern:** Preserve commutation under total trace normalization and recover
  an unnormalized moment by multiplication by the nonnegative actual trace.
- **Seen:** `TensorPower.pair_merge_moment_le_mul_trace`; the independent
  homogeneous merge-moment argument uses the same normalization calculation.
- **Abstraction:** Reuse the existing positive normalization, trace-one and
  reconstruction lemmas. Record a shared commutation lemma if further
  independent consumers appear; no general multiplicity interface is added.
- **Caveats:** At zero trace the positive matrix is zero and the normalized
  choice is a scalar identity. Empty bases require their own zero-matrix case.

### Composition of retained auxiliary traces — candidate (2026-10-08)

- **Pattern:** Regroup the auxiliary register by an explicit product equivalence, compose the partial traces of a rank-one density, then trace only the auxiliary factor of a proved Kronecker product.
- **Seen:** `Analysis/ReplicaJointDensity.lean`; regional product calculations appear in `Analysis/ReplicaRegionalDensity.lean`.
- **Abstraction:** Existing partial-trace composition and covariance results give the regrouping. The finite-sum Kronecker identity is private; no new tactic is introduced.
- **Caveat:** Retain the actual component and its own auxiliary density. A product identity is derived from the prescribed one-copy ground vector rather than supplied as a premise.

### Product-density invariance and actual trace mass — candidate (2026-10-08)

- **Pattern:** Identify each separate copy permutation with an operator on
  one factor tensored with the identity. Use `mul_kronecker_mul` to derive
  invariance of the actual product density, then partial-trace preservation
  and the unit one-copy trace to recover the component's squared norm.
- **Seen:** `Matrix.replicaGoodRegionalAuxiliaryMarginal_exp_mergeDeficit_le`
  in `QICLean/Analysis/ReplicaComponentMergeMoment.lean`; one mathematical
  consumer. The two separate actions use different factor invariances.
- **Abstraction:** Reuse the existing permutation entries, tensor-product
  multiplication, partial-trace preservation, and paired homogeneous moment
  theorem. The two elementary factor calculations remain private. No new
  tactic is introduced.
- **Caveats:** Both marginals must belong to the same excitation component.
  Retain the actual trace mass; do not assume a nonzero or unit component.

### Positive weighted trace of a difference square — candidate (2026-10-08)

- **Pattern:** Apply positive-semidefinite trace positivity to `(U - V)ᴴ * (U - V)`, then use Hermitian symmetry and commutation to identify the product terms and obtain the arithmetic-mean bound.
- **Seen:** `Analysis/WeightedTraceExponential.lean`; one calculation, reused for exponential matrices in the same file.
- **Abstraction:** The private product inequality isolates this calculation. Existing `Matrix.PosSemidef.trace_mul_nonneg` and exponential commutation identities supply the mathematical steps; no new tactic is needed.
- **Caveat:** Commutation of the two factors is a hypothesis, while no commutation with the positive semidefinite trace weight is used.

### Tensor-factor exponential and trace identities — candidate (2026-10-08)

- **Pattern:** Move a scalar through a Kronecker product, exponentiate the
  actual identity extension, and pair with a common matrix by partial trace.
- **Seen:** The common-space exponential and two complex trace equalities in
  `QICLean/Representation/PairMergeDeficit.lean`; their generic calculations
  already live in `KroneckerExponential.lean`, `TraceDistance.lean` and
  `Channel/PartialTrace.lean`.
- **Abstraction:** Use the existing exponential and trace-pairing theorems
  directly. No additional private helper or tactic is needed.
- **Caveats:** Operator factorization preserves correlations in the common
  matrix. It does not justify multiplying two marginal trace pairings.

### Simultaneous retained and discarded coordinate changes — candidate (2026-10-08)

- **Pattern:** Prove covariance of the literal excitation operator by its finite
  product entries, apply `submatrix_mulVec_equiv` to the actual component, and
  transport its partial trace using `partialTraceRight_submatrix_prod_equiv`.
- **Seen:** The exchanged common-density proof in
  `QICLean/Analysis/ReplicaGoodPairMarginal.lean`; one mathematical consumer.
- **Abstraction:** Private coordinate-covariance lemmas share the operator and
  vector calculation. Finite-sum reorderings use an explicit coordinate
  equivalence and `Equiv.sum_comp`, rather than a looping sum-commutation simp
  rule. No new tactic is introduced.
- **Caveats:** The physical and auxiliary regions are exchanged together; the
  component must be derived from the original vector and excitation operator.
  Neither normalization nor a supplied covariance identity is assumed.
  For a three-factor physical space, preserve the middle factor under the
  exterior-region exchange and trace all of its copies in the common density.

### Spectral projection on an intertwined range — candidate (2026-10-08)

- **Pattern:** Derive an actual matrix identity AT=TB with a positive B,
  transport the closed nonnegative indicator through the existing Hermitian
  functional-calculus intertwiner, and use the nonnegative spectrum of B.
- **Seen:** `Matrix.spectralProjectionGE_zero_mul_of_intertwine` in
  `QICLean/Analysis/SpectralProjectionIntertwiner.lean`; one mathematical
  application is being developed for complementary physical labels.
- **Abstraction:** Reuse `ConditionalMovement.QuantumSSA.cfc_intertwine`.
  The new projection theorem names the resulting spectral fact; no duplicate
  eigenbasis argument or tactic is introduced.
- **Caveats:** Derive the physical intertwining identity before applying the
  spectral fact. An independent middle physical region cannot be identified
  with the combined exterior region on the whole space.

### Excitation covariance under physical coordinate exchange — candidate (2026-10-08)

- **Pattern:** Transport the literal finite product of ground and defect factors through a one-copy coordinate equivalence, then transport the actual selected vector by `submatrix_mulVec_equiv`. A coordinate isometry preserves its Euclidean norm.
- **Seen:** `Analysis/ReplicaGoodPairMarginal.lean` and `Analysis/ReplicaTwoMergeMoment.lean`; two independent consumers, respectively the marginal exchange and its norm consequence.
- **Abstraction:** The existing matrix reindexing and coordinate isometry results supply the algebra. These two consumers retain private excitation calculations. Before a third consumer is added, extract their shared mathematical covariance statement and replace the repeated calculations.
- **Caveat:** Exchange both exterior physical and auxiliary regions while preserving the independent middle physical region. Derive covariance and simultaneous fixedness from actual coordinates; do not supply them as additional hypotheses.

### Chosen copy enumeration and actual density support — candidate (2026-10-08)

- **Pattern:** Transport an actual reduced density through a chosen finite-set
  enumeration, apply its proved product formula, and use a fixed tensor vector
  to show support in the physical symmetric subspace.
- **Seen:** `Matrix.symProj_mul_replicaExcitationComponent_goodAuxiliary_density`
  in `QICLean/Analysis/ReplicaGoodPhysicalSupport.lean`; one consumer.
- **Abstraction:** Reuse `partialTraceRight_submatrix_prod_equiv`,
  `Equiv.prod_comp`, `symProj_mulVec_of_mem`, `mul_vecMulVec` and
  `mul_kronecker_mul`. No new tactic or parallel marginal is introduced.
- **Caveats:** The product formula is derived from the actual excitation
  component. In Q tensor Y tensor V, every middle Y coordinate must be retained
  until physical symmetrization. The original vector need not be symmetric.

### Relative complementary labels and central-observable commutation — candidate (2026-10-08)

- **Pattern:** Apply the inversion-invariant central-coefficient identity to
  each column of an actual symmetric projection for a disjoint union, then
  sum the central projections with their real label weights. Extend actual
  nested/disjoint projector commutation to real label observables by finite
  sums and scalar multiplication.
- **Seen:** The private complementary-label and central-observable proofs in
  `QICLean/Representation/CompatiblePhysicalLabel.lean`, using the existing
  generic identities in `SchurLabelCommutation.lean` and finite-sum closure
  used in `LabelProjectors.lean`.
- **Abstraction:** Reuse the generic central-coefficient identity and
  `Commute.sum_left`, `Commute.sum_right`. One private observable helper
  treats nesting or disjointness, so the physical and both deficit
  applications do not repeat the projector-sum calculation. No tactic is
  introduced.
- **Caveats:** The complement is relative to the actual physical union QYV;
  it must retain Y as an independent factor. All source-facing commutation
  facts are derived for the five specified actions. No global positivity
  of the physical operator or preservation of the physical symmetric
  projection under a merge is assumed.

### Joint orthogonal-resolution coordinate functions — promoted lemmas (2026-10-08)

- **Pattern:** Form a product of commuting orthogonal resolutions and recover
  a function of either coordinate by summing the other resolution to the identity.
- **Seen:** `GroupedLabelEntropy.lean`, `SchurSurprisal.lean`,
  `MergeExponential.lean`, and `WeightedTraceHolder.lean`.
- **Abstraction:** `Matrix.IsOrthogonalResolution.prod_hom_fst` and
  `prod_hom_snd` in `Analysis/OrthogonalResolution.lean`. `MergeExponential.lean` and
  `WeightedTraceHolder.lean` use these two lemmas; the private helpers in
  `GroupedLabelEntropy.lean` and the joint calculations in `SchurSurprisal.lean`
  remain to be rewritten with them. This is a mathematical abstraction, with no new tactic.
- **Caveats:** The functions may be complex. Neither Hermiticity nor positivity
  is needed for the coordinate identities. The underlying projections must
  still form the actual resolutions; matrix order is obtained separately from
  scalar inequalities on nonzero joint components. No compatibility premise
  is added to any source theorem.

### Physical support through an auxiliary partial trace — candidate (2026-10-08)

- **Pattern:** Regroup the actual retained density, trace a discarded auxiliary
  factor, and move multiplication by a physical operator through this trace.
- **Seen:** `Analysis/ReplicaGoodConfigurationDensity.lean`; one consumer.
- **Abstraction:** Private finite-sum lemmas identify the literal rank-one
  trace and prove the left-multiplication identity. The coordinate transport
  is proved from permutation entries and their finite average. No new tactic
  is introduced.
- **Caveats:** All good middle physical coordinates are retained. The density
  and its support are derived from the same actual excitation component;
  neither a coordinate identity nor a support hypothesis is supplied.

### Logarithmic comparison on a nonzero joint eigenspace — candidate (2026-10-08)

- **Pattern:** From a positive eigenvalue r and the actual multiplicity inequality
  r d ≤ 1, use `Real.log_nonpos` and `Real.log_mul` to obtain log d ≤ −log r.
- **Seen:** The supported operator comparison in `Representation/SchurSurprisal.lean`
  and the positive exponential comparison in `Representation/SchurLabelMoments.lean`.
- **Abstraction:** These are two occurrences of the same scalar step. Existing
  logarithm and multiplication lemmas suffice for now. A third independent use
  should promote the supported scalar comparison beside the eigenvalue bound.
  The remainder-moment proof uses a different multiplicative exponential
  inequality and is not counted as another logarithmic comparison.
- **Caveat:** The zero-eigenvalue case must be treated separately. The comparison
  is used only on nonzero joint projections, never as a global label inequality.

### Hölder for a fixed family of subsystem observables — candidate (2026-10-08)

- **Pattern:** Extend actual nested/disjoint central-projector commutation to
  real label observables, verify the finite family of subsystem sets, and
  derive the commutation of signed sums before applying finite trace Hölder.
- **Seen:** `Representation/PhysicalMergeHolder.lean` uses the existing
  projector results in `SchurLabelCommutation.lean`. The private observable
  extension also occurs in `CompatiblePhysicalLabel.lean`; two occurrences
  in two files, below the threshold for a new public helper.
- **Abstraction:** Reuse `Commute.sum_left`, `Commute.sum_right` and direct
  addition/subtraction/negation closure. The five signed combinations share
  one private two-sided calculation. The general finite trace inequality
  remains in `Analysis/WeightedTraceHolder.lean`; no new tactic is introduced.
- **Caveats:** Derive every commutation from the actual subsystem actions.
  An arbitrary positive semidefinite trace weight need not commute with the
  observables. The factor Y is independent of the combined exterior QV.

### Reindexing sums and scalar multiples — existing lemmas (2026-10-09)

- **Pattern:** Apply a matrix reindexing identity to fixed row and column
  maps before simplifying a transported representation.
- **Seen:** The addition and scalar branches of
  `TensorPower.fiveFactorCopiesEquiv_auxiliary_groupAlgebraRep` in
  `QICLean/Analysis/FiveFactorAuxiliaryCoordinates.lean`, and the exponential
  transport in the separate `GroupedConfigurationTransport` contribution.
  `Matrix.PosDef.lower_pin_of_reindexed_inverse_compression` in
  `QICLean/Analysis/IsometricLowerPin.lean` also uses subtraction and scalar
  reindexing when transporting a positive matrix difference.
- **Abstraction:** Reuse Mathlib's `Matrix.submatrix_add`,
  `Matrix.submatrix_sub` and `Matrix.submatrix_smul`, followed by the
  corresponding `Pi.add_apply`, `Pi.sub_apply` or `Pi.smul_apply`.
  The matrix lemmas are equalities of functions of the two coordinate
  maps. Their applications must reduce before a transported matrix can
  match a previously established identity. No new tactic is needed.
- **Caveat:** When only an outer sum is to be transported, rewrite it once.
  Recursive simplification can expand the defining sum of a central
  observable and obscure the existing representation identity. For inverse
  coordinate equivalences, use `Equiv.symm_comp_self` before
  `Matrix.submatrix_id_id`; expanding composition into a lambda first can
  leave the identity reindexing unreduced.

### Symmetry of an excitation component under a copy subgroup — candidate (2026-10-09)

- **Pattern:** Prove that the subgroup preserves the actual excited subset,
  apply the existing covariance of the physical excitation operator, and
  transport the fixed-vector equation through the specified coordinate equivalence.
- **Seen:** `Analysis/ReplicaBadCopyExponential.lean`; the covariance is already
  provided by `Analysis/ReplicaExcitationSymmetry.lean`.
- **Abstraction:** Reuse `replicaExcitationProjection_kronecker_mulVec_preserves_fixed`
  and `Matrix.submatrix_mulVec_equiv`. The subset calculation is specific to
  the good/bad enumeration. No new tactic or general covariance result is needed.
- **Caveats:** The actual component may be zero. No component normalization,
  ambient positivity of a signed label entropy, or commutation of the excitation
  operator with a replica metric is introduced.

### Products of permutation indicators — existing Mathlib lemma (2026-10-09)

- **Pattern:** After transporting a permutation entry through a product
  coordinate equivalence, the entry is the indicator of a conjunction.
  A Kronecker product gives the product of the individual indicators.
- **Reuse:** `ite_zero_mul_ite_zero` combines these indicators directly.
  `Analysis/ReplicaBadCopyExponential.lean` uses
  `simp only [ite_zero_mul_ite_zero, one_mul]` for three factors.
- **Reason:** The former case split followed by unrestricted `simp_all`
  revisited universally quantified coordinate identities and exhausted
  the default heartbeat limit. The restricted existing identity closes
  the actual scalar goal without a new theorem, tactic, or larger limit.
- **Caveat:** First prove the actual coordinate equivalence and reduce the
  entries. The scalar identity supplies no permutation covariance itself.
### Auxiliary-label mass in compressed-site coordinates — candidate (2026-10-09)

- **Pattern:** Transport an eventual Schur projection-mass bound through the
  actual exterior coordinate isometry, retaining the same label sequence.
- **Seen:** `Representation/CompressedTypicalLabelSequence.lean` and
  `Representation/SchmidtBellCommonCutoffs.lean`; two occurrences in two files.
- **Abstraction:** Both use
  `TensorPower.norm_sq_labelProj_compressedTypicalSite_prod`, followed by
  reciprocal and natural-power coercion identities. A third independent use
  should supply a helper for the eventual inequality.
- **Caveats:** The mass belongs to the normalized selected state before any
  common regional cutoff. It is not a conditional mass after projecting,
  and no second label selection is made.
