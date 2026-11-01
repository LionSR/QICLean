# Tactic pattern ledger

Record repeated proof patterns before introducing a new tactic. Prefer an
existing theorem, then a reusable lemma or simp set; promote a new abstraction
only after at least three genuine occurrences across two files. Occurrences
in a regression file are not additional mathematical consumers.

## Promoted

### Dimension of a finite span of images — shared lemma (2026-10-27)

- **Pattern:** For a finite family of linear maps, bound the dimension of
  the sum of the images of a finite-dimensional subspace by the number of
  maps times the dimension of that subspace.
- **Reuse:** `Submodule.finrank_iSup_map_le_card_mul` in
  `Analysis/ViableSubspaceSpectralProjector.lean` combines
  `Submodule.finrank_iSup_le_sum` and `Submodule.finrank_map_le`.
  Neither ambient inner product space must be finite-dimensional; the
  index set may be empty.
- **Callers:** `Submodule.IsViable.map_of_tensor_decomposition`,
  `Submodule.IsViable.spectralProjector`,
  `Submodule.exists_isViable_finrank_le_half`, and
  `Submodule.viable_enlargement_of_close_improving_target`.
- **Decision:** Use the common lemma for the image-span dimension estimate,
  then apply any separate bound on the dimension of the initial subspace.


### Fixed-effect transfer under trace-norm error — existing lemma (2026-10-29)

- **Seen:** `Entropy/SpectralTail.lean` and
  `Channel/PureMarginalApproximation.lean`.
- **Reuse:** `Matrix.re_trace_mul_sub_le_traceDistance` bounds the change of an
  actual effect's expectation for equal-trace Hermitian matrices. Positivity
  and the upper bound by the identity replace any commutation requirement.
- **Owner:** The unchanged theorem moves to `Analysis/TraceDistance.lean`,
  already imported by the spectral-tail module. The channel argument reuses
  its proof rather than repeating a Jordan-part expansion or importing entropy.

### Full row rank gives surjectivity — existing Mathlib lemma (2026-10-27)

- **Seen:** The equal-dimensional isometry argument in
  `Algebra/MatrixUnitaryBetween.lean` and the minimal Stinespring argument in
  `Channel/OrderedCP.lean`.
- **Reuse:** `Matrix.mulVec_surjective_iff_rank_eq_card` applies directly to
  their existing full-row-rank equalities. It replaces a manual injectivity
  and dimension comparison, and a manual range-dimension argument.
- **Decision:** Reuse Mathlib's theorem; no local wrapper or tactic is added.
  Empty finite index types are still admitted.

### Trace normalization of a bipartite unit vector — shared lemma (2026-10-23)

- **Seen:** The orthogonal-decomposition quotient and geometric-tail theorem in
  `Channel.AGSPGeometricTails`, and the rank-one endpoint and favorable entropy
  theorem in `Channel.AGSPFavorableEntropy`; four callers across two files.
- **Decision:** Use
  `Matrix.trace_schmidtCoeffMatrix_mul_conjTranspose_of_norm_one` for the complex
  trace. For its real part, apply `congrArg Complex.re` and simplify
  `Complex.one_re`.
- **Reused:** `Matrix.normSq_toEuclid`, trace cyclicity and
  `Matrix.IsHermitian.trace_eq_ofReal_re` identify the trace with the squared
  norm of the original vector. No supplied density normalization is assumed.
- **Callers:** `one_sub_kyFanNorm_le_of_orthogonal_decomposition`,
  `sum_eigenvalues_geometric_tail_of_operatorSchmidtRank`,
  `vonNeumannEntropy_reduced_eq_zero_of_operatorSchmidtRank_le_one`, and
  `vonNeumannEntropy_reduced_le_four_log_of_operatorSchmidtRank`.

### Support of an eigenvector with positive eigenvalue — existing scalar cancellation (2026-10-26)

- **Seen:** The positive-eigenvalue range argument in `Channel/LeadingEigenvector.lean`
  and the support constraint in `Channel/BoundaryDensitySelection.lean`.
- **Reuse:** Apply `congrArg` to the matrix support equation, then use
  `Matrix.mulVec_mulVec`, `Matrix.mulVec_smul` and `smul_right_injective`.
- **Scope:** Cancellation concerns the nonzero eigenvalue. Neither invertibility
  of the density matrix nor a projection hypothesis on the support matrix is needed.
- **Decision:** Reuse scalar cancellation directly; no additional definition or
  proof automation is introduced.

### Coordinate transport and identity factors — existing Mathlib structures (2026-10-26)

- **Seen:** The matrix expectations and identity-factor norm comparison in
  TNLean's chain gluing argument, now stated in `Analysis/EuclideanReindex.lean`
  and `Analysis/KroneckerOperatorNorm.lean`.
- **Reuse:** `LinearIsometryEquiv.piLpCongrLeft.inner_map_map` and
  `Matrix.submatrix_mulVec_equiv` replace coordinatewise sums. Injectivity of
  `Matrix.rightKroneckerEmbed` permits `NonUnitalStarAlgHom.norm_map` to replace
  the corner-norm calculation.
- **Decision:** These two matrix statements are shared. Inner-product transport
  and the rank-one trace identity use existing Mathlib results directly in
  later consumers; no additional wrappers or custom tactics are introduced.

### Coefficients after left multiplication by a linear polynomial — promoted (2026-10-22)

- **Consumers:** The ordered-gap equality in `Algebra/OrderedPolynomialGaps.lean`,
  the commuting-gap span in `Algebra/CommutingPolynomialGaps.lean`, and the
  two-marker identity in `Algebra/PolynomialTwoMarkerPower.lean`.
- **Lemma:** `Polynomial.coeff_C_add_C_mul_X_mul_succ` in
  `Algebra/PolynomialLinearFactor.lean` gives the successor coefficient of
  `(C D + C T * X) * P` over an arbitrary semiring. It combines the existing
  constant and monomial coefficient identities without reordering products.
- **Refactor:** Both gap recurrences invoke the shared lemma after expanding
  the power on the left. The two-marker proof uses the same coefficient rule
  over the polynomial semiring and over its coefficient semiring; its distinct
  induction is retained.
- **Accounting:** There are three production consumers across three files.
  The two-marker boundary applications are fixtures, not additional consumers.
  This entry consolidates the two previously overlapping candidate entries.
- **Scope:** Only addition may be reordered. The existing constant and leading
  coefficient arguments remain separate; no coefficient-commutativity premise,
  custom tactic or additional polynomial framework is introduced.

### Finite linear combinations in an operator-block span — existing Mathlib lemma (2026-10-22)

- **Consumers:** Both cut-movement proofs in `Algebra/OperatorSchmidtCut.lean`
  the middle-block expansion in `Algebra/OperatorSchmidtTwoCuts.lean`, and
  the extracted gap blocks in `Algebra/LocalPolynomialSchmidtRank.lean`.
- **Lemma:** `Submodule.sum_smul_mem` handles the scalar-weighted finite sum;
  each caller supplies membership of the actual family in its span.
- **Refactor:** Replace the repeated sum-closure and scalar-closure steps by
  this existing lemma. The cut statements and their hypotheses are unchanged.

### Operator Schmidt rank from a finite block span — promoted (2026-10-22)

- **Consumers:** The product-decomposition bound in `Algebra/OperatorSchmidt.lean`
  both cut-movement bounds in `Algebra/OperatorSchmidtCut.lean`, and the
  coefficient gap bound in `Algebra/LocalPolynomialSchmidtRank.lean`.
- **Lemma:** `Matrix.operatorSchmidtRank_le_card_of_blocks_mem_span` combines
  inclusion of block spans with the dimension bound for a finite spanning family.
- **Refactor:** Each consumer supplies its actual block expansion. The existing
  product-decomposition theorem keeps its statement; the two cut bounds derive
  their spanning families from a shortest decomposition.
- **Scope:** The shared lemma holds over an arbitrary field, including empty
  finite factors. No additional spanning assumption enters the cut bounds.


### Entropy comparison with a supplied uniform norm bound — shared private lemma (2026-10-18)

- **Seen:** The polynomial and logarithmic buffered-discount theorems in
  `Entropy.BufferDiscount`; two energy envelopes in one file.
- **Decision:** Share the positive single-filter bounds, trial/Schmidt
  comparison, logarithm calculation and entropy rearrangement. Each
  wrapper proves the uniform norm comparison for the same actual
  zero-floor family using its own energy estimate.
- **Caveat:** The callback is private. Neither public theorem assumes a
  norm-comparison witness or clipping at floor zero. The energy budget
  and local bounds remain independent of the raised positive floors.
- **Scalar step:** A private scalar lemma derives crossing smallness
  from the existing tail-radius admissibility. Its real parameter is
  generic; no positivity of a marginal eigenvalue is required.
- **Reused:** Existing `Function.ne_iff` and `WithLp.ofLp_eq_zero` supply
  configuration witnesses without another coordinatewise contradiction.

### Prefix comparison for the actual maximizing family — shared private lemma (2026-10-18)

- **Seen:** The polynomial and logarithmic successor comparisons in
  `Entropy.FilterPrefix`; two energy budgets in one file.
- **Decision:** One private lemma selects an actual maximizing prefix and
  applies the energy estimate to that same family and its normalized
  output. The gap and existing overlap comparison finish the argument.
- **Caveat:** The core requires no global upper-weight bound or sign on
  the energy budget. Strict `E < Δ` enters only in the later floor-zero
  division. Existing physical statements retain their original ranges.
- **Iteration:** Reuse `pow_mul_le_prod_of_step` and
  `norm_le_of_forall_floor`; no new telescoping or continuity machinery.

### Configuration witnesses from nonzero vectors — existing Mathlib lemmas (2026-10-18)

- **Seen:** The shared successor, its physical callers and the new
  logarithmic floor-zero comparison in `FilterPrefix` and `FilterZeroFloor`.
- **Decision:** Reuse `WithLp.ofLp_eq_zero` at exponent two and
  `Function.ne_iff`. This replaces the repeated coordinatewise
  contradiction proof with existing mathematical lemmas.
- **Caveat:** The coordinate supplies only the existing configuration
  witness. No nonempty-space premise or physical witness structure is
  added, and no nonvanishing coordinate enters the energy statement.

### Summing termwise conjugation bounds — shared private lemma (2026-10-18)

- **Seen:** The polynomial and logarithmic stationary energy estimates in
  `Entropy.FilterChainEnergy`; two numerical envelopes in one file.
- **Decision:** One private mathematical lemma converts a conjugated
  eigenvector equation and termwise bounds into an energy sum over the
  actual crossing pairs. The caller supplies its envelope.
- **Caveat:** Linearity and the crossing-index interchange require neither
  positivity of the envelope nor additional spectral hypotheses.

### Normalization of the actual maximizing output — shared private lemma (2026-10-18)

- **Seen:** Coarse, sharp polynomial and logarithmic maximizer estimates in
  `Entropy.FilterChainEnergy`; three consumers in one file.
- **Decision:** Derive invertibility, unit normalization, common-basis
  clipping and inverse-product cancellation once for the actual output.
  Each energy theorem supplies its own numerical estimate.
- **Caveat:** Positive floors and maximality give these conclusions; they
  are not supplied output assumptions. No global weight upper bound is
  needed for this common construction. Existing ranges are preserved.

### Numerical bounds after stripping a nested filter product — shared private lemma (2026-10-18)

- **Seen:** The sharp polynomial and logarithmic conjugation estimates in
  `Entropy.FilterChainEnergy`; two numerical applications in one file.
- **Decision:** Reuse one private mathematical reduction with an arbitrary
  local expectation envelope. Containing filters preserve the expectation;
  disjoint filters commute with the supported observable. At most one
  splitting filter remains.
- **Caveat:** Nonnegativity of the envelope is derived from its local
  absolute-value bound. This introduces no sign assumption on the weights
  of the existing sharp theorem and no smallness outside splitting regions.
- **Mechanism:** The existing sharp and coarse public results keep their
  statements; the coarse theorem uses the sharp one. No tactic or new
  filter predicate is introduced.

### Transport of a finite product decomposition — promoted lemma (2026-10-18)

- **Seen:** `Entropy.hasProductDecomposition_conj` and both common-basis
  conjugation estimates in `FilterEnergy.lean`: three finite-sum calculations
  across two files.
- **Lemma:** `Entropy.cutBasisChange_conj_sum_kronecker` transports the same
  factors termwise. The existing one-term conjugation identity and
  norm-contraction lemma supply the algebra and the bounds; no fresh
  decomposition is chosen.
- **Refactor:** All three finite-sum calculations invoke this direct equality.
- **Caveat:** The equality itself needs no unitary assumption. Unitarity is
  used separately for norm bounds and invariance of expectations.

### Conditional filtered Gram moments — promoted lemma (2026-10-17)

- **Pattern:** Derive the lower trace-pairing bound, use its strict positivity
  to prove positivity of the filtered Gram moment, and apply the entropy upper
  bound at the optimizer weights. `optimizer_attains` identifies the last trace.
- **Result:** `ConditionalMovement.ConditionalCollision.conditional_gramMoment_bounds`
  in `Entropy/ConditionalMovement/Optimizer.lean`, after `density_spectrum_sum`.
  It returns the lower bound, positivity and the entropy upper bound together.
- **Consumers:** `conditional_optimizer_root_stability` in `Optimizer.lean` and
  `conditional_optimizer_deficit` in `FilterSlack.lean` use the lower and upper
  bounds. Their eigenvalue nonnegativity and spectral mass remain available for
  the final optimizer estimates. `paired_entropy_boundary` in
  `BoundaryEnergy.lean` uses positivity and the upper bound.
- **Scope:** The marginal may be singular. The lemma retains normalization, a
  nonempty first coordinate type, `0 < β ≤ 1/3`, and
  `β / (1 - β) * log (card X) ≤ 1`. No consumer gains a hypothesis or import.
  One mathematical lemma removes the repeated argument; no tactic is introduced.

### Reciprocal real powers — existing mathematical lemma (2026-10-16)

- **Pattern:** Normalize or reconstruct a nonnegative eigenvalue by composing
  real powers whose exponents multiply to one.
- **Consumers:** `IsFeasibleFilter.of_common_basis` in `FilterOptimizer` and
  `IsFeasibleFilter.trace_cfc_rpow` / `isFeasibleFilter_zero_iff` in
  `FilterFeasibility`.
- **Decision:** Reuse `Real.rpow_mul`, followed by the scalar reciprocal
  identity and `Real.rpow_one`. No new tactic or duplicate power theorem is
  needed, and the existing provider is unchanged.
- **Caveat:** Keep the nonnegative-base premise and the nonzero denominator.
  Replacing this calculation by an exponential-of-log convention changes
  its value at zero and is invalid for singular filters.

### Ordered products of rectangular intertwiners — promoted (2026-10-12)

- **Pattern:** From `A g * Z = Z * B g` for every factor, derive the same
  equation for the two ordered products. Three proofs used
  `List.prod_hom_rel`, the same rectangular associativity calculation, and
  `List.map_ofFn`.
- **Result:** `Matrix.listProd_ofFn_intertwine` in
  `QICLean/Algebra/MatrixProductIntertwine.lean`, over an arbitrary semiring
  and arbitrary finite row and column index types.
- **Consumers:** `ReplicaSymmetricMeanTreeProduct`,
  `BellPinnedCompressedPowers`, and `ReplicaTransport/RootCompression`.
  Each now applies the common lemma once.
- **Decision:** A mathematical lemma suffices; no tactic is introduced.
  It preserves the original order, including an empty product, and needs
  no positivity, commutation, nonempty coordinate set, or isometry.
  `BellPinnedProductAction` retains its separate direct use of
  `List.rel_prod`; positivity of its exterior product is proved separately.

No new tactic or automation is introduced for shifted spectral truncation.
The proofs reuse existing functional-calculus identities, projection
rank/trace comparison, range-of-composition, and scalar real-power bounds.

### The invariant projector is an orthogonal projection — promoted (2026-10-12)

- **Pattern:** Obtain a label `l₀` from `exists_labelProj_eq_symProj`,
  rewrite the invariant projector as `labelProj φ l₀`, and assemble
  `IsStarProjection` from `labelProj_mul_self` and `isHermitian_labelProj`.
- **Result:** `PermutationRepresentation.isStarProjection_symProj` in
  `QICLean/Representation/TrivialLabel.lean`, for every finite group and
  permutation action.
- **Consumers:** `ReplicaBadCopyExponential`, `GroupedLabelSymmetricSupport`,
  `ReplicaLowDefectProjection`, `RegionalLowDefectProjection`,
  `ReplicaSymmetricMetricFloor` (twice) and
  `ReplicaLowDefectSymmetricCoordinates`, and
  `BellPinnedCompressedPowers` (the idempotence field).
- **Decision:** A lemma suffices; no tactic is introduced. The remaining
  inline derivations in the Bell-pinned modules can switch to the lemma
  when those modules are next edited.

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

### Hermitian rectangular intertwiners — promoted mathematical lemmas

- **Pattern:** From `A * J = J * B` for Hermitian matrices, move the adjoint
  intertwiner through the matrices and transport sandwiches `J * H * Jᴴ`.
- **Consumers:** Power-derivative covariance, geometric-mean derivative
  covariance, and mean-tree derivative and leaf-map covariance.
- **Abstraction:** Reuse `Matrix.IsHermitian.conjTranspose_intertwine` and
  `Matrix.IsHermitian.sandwich_intertwine` from
  `QICLean/Algebra/MatrixSandwichIntertwine.lean`. Compression identities use
  the same embedding lemmas with `Jᴴ`.
- **Caveats:** These are algebraic identities for rectangular intertwiners.
  Norm preservation requires an isometry; positivity of a compressed operator
  does not identify its inverse with a compressed inverse.

## Candidates

### Matrix coefficients as continuous linear functionals (2026-10-28)

- **Seen:** `Analysis/GaussianFilter/MatrixIntegral.lean`,
  `Analysis/SpectralFilter/MatrixFilter.lean`, and
  `Analysis/Transport/NormDerivative.lean` each construct the linear functional
  `A ↦ star v ⬝ᵥ (A *ᵥ w)` by supplying linearity proofs.
- **Replacement:** Compose Mathlib's `dotProductBilin` with the partial
  evaluation `(Matrix.mulVecBilin ℂ ℂ).flip w`, then apply
  `LinearMap.toContinuousLinearMap` in finite dimension.
- **Decision:** `Analysis/GaussianFilter/CommutatorSeries.lean` uses this
  composition. No fourth handwritten linearity proof or new public
  abstraction is introduced. The three existing constructions can be
  simplified separately after checking their imports and scalar conventions.

### Convexity from a quadratic variational formula (2026-10-29)

- **Seen:** The trace-exponential variational argument in
  `Analysis/LiebTraceExponential.lean` and the Ando--Lieb power functional in
  `Analysis/LiebConvexity.lean` evaluate a variational bound at the optimizer
  of a convex combination, then apply a known convexity or concavity inequality.
- **Reuse:** Trace cyclicity, `Matrix.trace_conjTranspose`, and positivity of
  the trace product give the completed-square bound for the power functional.
- **Decision:** These are two mathematically distinct variational formulas.
  Keep their optimizers explicit; no tactic or additional abstraction is needed.

### Orthogonal component along a unit eigenvector (2026-10-26)

- **Seen:** The final decomposition in `Analysis/GapPerturbation.lean` and the
  overlap-to-energy estimate in `Analysis/OverlapEnergy.lean` write
  `v = ⟪Ω, v⟫ • Ω + w` and apply Pythagoras to obtain
  `‖w‖² = ‖v‖² - ‖⟪Ω, v⟫‖²` for unit `Ω`.
- **Reuse:** Both energy arguments use `re_inner_smul_add_eigenvector` for
  the quadratic form. The elementary orthogonality and norm calculation
  remains at its two sites; seek a Mathlib projection lemma before adding
  another local calculation or a new helper.

### Sharp product-overlap inequality — shared private lemma (2026-10-23)

- **Pattern:** Choose an actual unit Schmidt-rank-one maximizer, decompose it
  into its component along the fixed vector and its perpendicular remainder,
  and apply the rank-overlap estimate to the image of that same maximizer.
- **Seen:** The quantitative product-overlap theorem and the rank-one endpoint
  in `Channel/ProductOverlapBootstrap.lean`.
- **Abstraction:** `exists_unit_rank_one_overlap_bootstrap` contains the common
  argument once. The former theorem applies its numerical tradeoff afterward;
  the endpoint instead uses strict contraction to make the remainder vanish.
- **Notes:** These are two consumers in one file, below the tactic-promotion
  threshold. An ordinary helper theorem suffices; no tactic is introduced.
  The public homogeneous contraction lemma is available to the separate
  powered-vector argument. Regression applications are not counted as consumers.

### Positivity of a filtered Gram moment — legacy candidate (2026-10-17)

- **Pattern:** A positive power of a nonnegative Gram moment forces the moment
  to be positive: otherwise it is zero, and its positive power vanishes.
- **Seen:** `gramMoment_pos_of_filter_pos` and `optimizer_root_bound` in
  `Entropy/ConditionalMovement/Optimizer.lean`, and `optimizer_deficit_bound` in
  `Entropy/ConditionalMovement/FilterSlack.lean`.
- **Decision:** These three preexisting contradiction arguments remain unchanged.
  A later simplification should first check a suitable real-power positivity
  lemma and reuse the weakest existing result; no additional analytic bound or
  new tactic is needed. This candidate is separate from the shared conditional
  lower/upper trace estimates above.

### Scalar phase-power identities — legacy candidate (2026-10-17)

- **Pattern:** After expanding a spectral phase product, move real coercions into
  the complex exponent and close the scalar polynomial identity.
- **Seen:** `phase_mul_power` and `power_mul_phase` in
  `Entropy/ConditionalMovement/BoundaryEnergy.lean`.
- **Decision:** These two preexisting cast-and-ring calculations remain unchanged.
  Two occurrences in one file do not require a new abstraction. Reuse the
  existing phase-power identities in later consumers instead of copying them.

### Product decompositions under tensor permutations and identity spectators — candidate (2026-10-22)

- **Seen:** The factor-flip inequality and the left and reflected right
  spectator inequalities in `Algebra/TripartitePolynomialSchmidtRank.lean`.
- **Pattern:** Choose an actual shortest product decomposition, identify the
  transformed tensor factors termwise, and apply the existing upper bound
  for the length of a product decomposition.
- **Decision:** The three tensor identities are in one module. Reuse
  `Matrix.hasOperatorSchmidtDecomposition_operatorSchmidtRank` and
  `Matrix.operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition`;
  keep the distinct tensor identities explicit. No additional tactic is needed.
- **Caveat:** An empty spectator may lower the rank. Only the displayed
  decomposition length is preserved; no nonempty-factor premise or rank
  cancellation is used. Boundary applications are not additional consumers.


### Finite scalar span followed by an operator-rank sum — candidate (2026-10-22)

- **Seen:** The final coefficients in `Algebra/CommutingPolynomialSchmidtRank.lean`
  and `Algebra/LocalPolynomialSchmidtRank.lean`.
- **Pattern:** Use `Submodule.mem_span_range_iff_exists_fun` to obtain the actual
  complex scalar coefficients, then the scalar and finite-sum rank bounds.
- **Decision:** Two occurrences; retain the direct arguments. A third consumer
  would justify a rank bound for membership in a finite operator span.
- **Caveat:** In the local-polynomial argument, coefficient extraction is first
  justified by a fixed tensor-factor family; a pointwise rank hypothesis alone
  does not justify that step.

### Normalized regional states — candidate (2026-10-15)

- **Pattern:** Expand the normalized patch output and use `regionState_smul`
  to express its regional matrix as the unnormalized regional matrix times
  the squared inverse norm. The multiplier is nonnegative even at zero output.
- **Seen:** `Entropy.patch_stationarity` in `Entropy/PatchStationarity.lean`
  and `Entropy.re_trace_variation_le_of_isPatchMinimizer` in
  `Entropy/PatchNormalizedFirstVariation.lean`.
- **Abstraction:** Both proofs reuse `regionState_smul`. A third occurrence
  would justify a direct regional-state identity for `patchState`.
- **Caveat:** Multiplication by the squared inverse norm is valid at zero;
  cancelling the norm would require a separate nonvanishing argument.

### Products preserving common spectral cutoffs — candidate (2026-10-11)

- **Pattern:** Prove that each factor preserves a common fixed subspace and
  bounds the norm there, then compose the estimates in the prescribed order.
- **Seen:** The two inverse metrics and the direct metric in
  `Representation/ReplicaPinnedLeafExpectation.lean`; one mathematical
  application with three factors in one file.
- **Abstraction:** The private lemmas `norm_mul_on_invariant` and
  `norm_listProd_on_invariant` express composition and finite iteration.
  Preservation follows from the existing commutation theorem for nested
  or disjoint subsystems. A second independent application may justify
  exposing these elementary matrix lemmas; no custom tactic is introduced.
- **Caveat:** Bounds on individual vectors do not compose without the
  preservation statement. Commutation is derived from the actual region
  relations and does not extend to arbitrary overlapping regions.

### Projection coefficients and exponential rates — candidate (2026-10-11)

- **Pattern:** Take the logarithm of a positive product of polynomial and
  exponential factors, identify it with a remainder minus the leading
  rate, and express the reciprocal coefficient as the corresponding
  exponential lower bound.
- **Seen:** The rough and sharp norm comparisons in
  `Analysis/RegionalRoughLowerNorm.lean` and
  `Analysis/RegionalSharpLowerNorm.lean` have two occurrences. The sharp
  rate also includes the variance correction.
- **Abstraction:** Existing `Real.log_mul`, `Real.log_rpow`,
  `Real.exp_log` and polynomial normalization suffice for these two uses.
  A third independent occurrence would justify a common scalar lemma;
  no new tactic is introduced.
- **Caveat:** Positivity is proved for the actual coefficient. The sharp
  variance term is retained exactly when its logarithm is normalized.

### A common polynomial exponent over finitely many cuts — candidate (2026-10-11)

- **Pattern:** Choose each regional exponent, take the maximum of their finite
  family and zero, and increase the positive-base power before taking its
  reciprocal in an operator lower bound.
- **Seen:** The rough and sharp theorems in
  `QICLean/Analysis/RegionalLowDefectLowerPin.lean` have two occurrences in
  one file. The matrix-order transport itself is already shared through
  `regional_lower_pin_pullback`.
- **Abstraction:** The current proofs use `Finset.le_sup'`,
  `Real.rpow_le_rpow_of_exponent_le`, and the shared pullback. A third
  occurrence in another file would justify a common finite-family helper.
- **Caveat:** Only the polynomial exponent is absorbed; the exponential
  subset count and the variance term remain in the coefficient.

### Replica regions with two auxiliary sites — shared geometric statement (2026-10-11)

- **Pattern:** Lift physical regions to the common site family, adjoin the
  left auxiliary site, and identify the far factor as the complement of
  the lifted left and middle regions. Transport the given cross-band
  nesting through the same physical inclusion.
- **Consumers:** The normalized product-mass estimate and the rough and
  sharp lower-norm applications require these same three conclusions.
- **Decision:** `TensorPower.replicaMetric_lifted_region_geometry` states
  them together in `Representation/RegionalReplicaMetricRegions.lean`.
  Its proof uses finite-set membership and monotonicity of images and
  insertion; no custom tactic is introduced.
- **Caveat:** The nesting hypothesis ranges over every pair of terminal
  labels in distinct ordered bands. No comparison between labels in the
  same band is required.

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


### Scalar multiplication in partially applied matrix coordinates — candidate (2026-10-09)

- **Pattern:** After rewriting `submatrix_smul`, a coordinate equivalence may
  still be supplied as a partially applied function. Scalar multiplication
  then needs evaluation at both matrix indices before an existing coordinate
  identity matches.
- **Seen:** The singleton exponential transport in
  `QICLean/Analysis/ReplicaGoodConfigurationSingletonMoment.lean`, both for the
  five-factor coordinates and for the physical singleton coordinates.
- **Abstraction:** Reuse Mathlib's `Pi.smul_apply`, followed by the existing
  `Matrix.reindex_exp` and `Matrix.exp_kronecker_one` identities. The group
  algebra comparison uses canonical finite-function and product decidable
  equality instances, matching the existing product-action theorem.
  No new tactic, global instance, or mathematical comparison is introduced.
- **Caveats:** Distinguish a partially applied coordinate function from a
  matrix entry; entrywise matrix expressions use the existing `Matrix.*_apply`
  lemmas instead.

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
  `kronecker_mulVec_product` lemma. The public supplied-label theorem
  reuses this identity with explicit vector arguments and lifts the two
  auxiliary fixed-vector equalities through the physical product factor.
  The mean-energy calculation in
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
  `MergeExponential.lean`, `WeightedTraceHolder.lean`,
  `ReplicaWholeInverse.lean`, and `ReplicaPinnedMetricUpper.lean`.
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
- **Local repetition (2026-10-13):** The three coordinate identities in
  `ReplicaPinnedMetricUpper.lean` repeat local names for the same three
  resolutions and their first product. All three calculations already use
  `prod_hom_fst` and `prod_hom_snd`; no finite-sum argument is copied.
  This repetition occurs within one proof and does not warrant another
  general lemma or tactic.

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
- **Further use:** `Representation/CompressedTypicalExponential.lean`
  transports the exponential of the regional label entropy by
  `Matrix.reindex_exp` and the same scalar-submatrix identities. The
  tensor-density identity follows entrywise from `Matrix.finKronecker_apply`
  and the actual one-copy marginal identity. The final trace transport
  reuses `Matrix.submatrix_mul_equiv` and `Matrix.trace_reindex`.

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

### Central observables after restricting the copy action — shared theorem (2026-10-09)

- **Pattern:** Factor a larger subsystem action into a smaller subsystem and
  its disjoint complement, then pass centrality through the group algebra.
- **Reuse:** `TensorPower.commute_subgroup_labelObservables_of_subset_or_disjoint`
  in `Representation/SubsystemLabelCommutation.lean` treats a common arbitrary
  homomorphism of copy permutation groups. The laminar band argument specializes
  it to the identity homomorphism and reverses the nested case when required.
  The joint auxiliary exponential contribution uses the same theorem for the
  actual good-copy subgroup, replacing its private copy.
- **Caveats:** Both actions use the same restriction homomorphism. No injectivity,
  nonempty local-space assumption, or commutation of arbitrary overlapping
  subsystems is inferred. Symmetric-range commutation separately reuses the
  existing subgroup projection theorem from `GroupedLabelSymmetricSupport`.

### Projections under equivariant coordinates

The original replica cutoff uses the same two elementary arguments in its
five-factor and global coordinates. Equivariant permutation matrices transport
the group average; `PermutationRepresentation.symProj_of_intertwine` records
this once. A contained projection then remains a projection after compression
by the same rectangular coordinate map; use
`Matrix.isStarProjection_conjTranspose_mul_mul_of_mul_range_eq` in
`Algebra/OrthogonalProjection.lean`. The latter needs only `P * (Z * Zᴴ) = P`,
not a separate isometry identity or commutation with a metric. The regional
cutoff covariance applies these arguments to the actual rank-one ground
projector, the defect cutoff, and the original auxiliary labels.

### Functional calculus on two complementary sectors — existing lemma (2026-10-09)

- **Pattern:** Regard a self-adjoint idempotent and its complement as a finite
  orthogonal resolution, then apply scalar functional calculus to the two
  assigned values.
- **Seen:** `Matrix.cfc_affine_of_isSelfAdjoint_isIdempotentElem` in
  `QICLean/Analysis/ProjectionCalculus.lean`.
- **Abstraction:** Reuse `Matrix.IsOrthogonalResolution.cfc_hom`; no new tactic
  or separate continuity argument is required.
- **Caveats:** Scalar values may coincide, and projection ranges may be zero.
  Positivity needed for later logarithmic comparisons belongs to those
  comparisons, rather than this general calculation.
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

### Instances for a finite family of coordinate spaces — candidate (2026-10-09)

- **Pattern:** Construct Fintype, DecidableEq and Nonempty instances for a
  dependent family with five explicitly specified fibers.
- **Seen:** The three instances in
  `Representation/RegionalFiveFactorCoordinates.lean`; one file.
- **Reuse:** Use the existing dependent eliminator `Fin.cases`, with
  `inferInstanceAs` naming each actual fiber and `fun i => Fin.elim0 i`
  for the empty final case. This preserves the canonical component
  instances and handles families valued in Type as well as Prop.
- **Reason:** A `fin_cases` proof through list membership cannot eliminate
  that proposition into these Type-valued instances. Merely unfolding the
  family leaves vector notation at the instance-synthesis boundary.
- **Decision:** No new tactic or finite-family abstraction is introduced.
  These three uses are in one structural definition; reconsider only if
  another family produces independent repetition.

### Scalar identities after adding matrix inequalities — candidate (2026-10-09)

- **Pattern:** Add and rescale inequalities in the matrix order, then identify
  the resulting linear combination with the desired expression by `module`.
- **Seen:** `Analysis/FloorPin.lean`, in `floor_pin_le` and
  `identity_extension_floor`; two occurrences in one file.
- **Abstraction:** The standard order lemmas and `module` suffice. A further
  independent occurrence may justify a helper for the shared scalar identity.
- **Caveats:** Nonnegative scalar multiplication is established before the
  algebraic conversion. No projection or commutation assumption is needed
  for these two additive comparisons.
### Chronological prefix and suffix coordinates — candidate (2026-10-09)

- **Pattern:** Express a retained prefix as the predicate filter of the original
  prefix, and a full suffix as the corresponding list drop.
- **Seen:** The consecutive-difference calculation and both endpoint
  calculations in `PoissonWord.foldl_sub_partitionWords_fst_eq_sum`, in
  `QICLean/Probability/PoissonWordTelescope.lean`; three occurrences in one file.
- **Abstraction:** Reuse `ofFn_partitionWords_fst`, `ofFn_take`, and `ofFn_drop`
  with `simp only`. A further lemma or simp set is deferred until the pattern
  also occurs in a second file.
- **Caveats:** Normalize the word coordinates before simplifying list maps.
  Otherwise `List.map_ofFn` can remove the form needed for the filter identity.
  Full suffixes and retained prefixes refer to the same original word.

### Contractive chronological folds — candidate (2026-10-09)

- **Pattern:** A fold of maps satisfying `‖E i y‖ ≤ ‖y‖` preserves the norm
  bound of its initial vector.
- **Seen:** The local `hact` arguments in `PoissonWordOmissionBound.lean` and
  `PoissonWordExpectedOmission.lean`; two occurrences in two files.
- **Abstraction:** Reuse `List.foldlRecOn` with the invariant `‖z‖ ≤ ‖y‖`.
  A general norm inequality for folds should be considered at a third occurrence.
- **Caveats:** No norm compatibility with the scalar action is needed; the
  contraction hypothesis concerns the additive seminorm directly.

### Logarithmic consequences of positive overlap bounds — existing lemmas (2026-10-12)

The scalar Bell-overlap estimate derives positivity before using
`Real.log_le_log`. Existing logarithm rules for products, quotients,
natural powers, real powers and exponentials give the exact leading term.
Monotonicity then bounds the polynomial error uniformly in the inverse-power
exponent. No new logarithm tactic is needed.

### Natural-count logarithmic remainders — candidate (2026-10-12)

- **Pattern:** Show that a fixed linear combination of 1/k and
  log(k+a)/k tends to zero along natural replica counts.
- **Consumers:** `Real.tendsto_bellOverlapRemainder` in
  `Analysis/BellOverlapLogBound.lean` and the private shifted-log lemma
  in `Analysis/MeanTreeSublinearRemainder.lean`.
- **Existing result:** Specialize
  `Real.tendsto_pow_log_div_mul_add_atTop` to `(1, -a, 1)` and compose
  with natural-number coercion followed by addition of `a`. Use
  `tendsto_inv_atTop_zero` for the constant term.
- **Decision:** Two independent proofs have been identified. Reusing the
  private shifted-log lemma twice is not a third proof. Record the
  pattern without introducing a new tactic; a third independent use
  would justify one shared shifted-log limit theorem.
- **Caveat:** Every coefficient is fixed before the replica count tends
  to infinity. This argument gives no uniform threshold over varying
  dimensions or polynomial degrees.

### Bell restriction of positive mean trees — existing lemmas (2026-10-11)

The metric restriction uses `IsHermitian.conjTranspose_intertwine` for the
adjoint equation and `Matrix.MeanTree.eval_intertwine` for the same tree of
positive factors. Its real powers use `PosSemidef.rpow_intertwine`.
Full-copy symmetry commutation is the containing-subsystem label theorem
with the full subsystem; the group-algebra argument is not repeated.
The inserted vector need not be unit for these identities. Unit norm is
used only to conclude that the inserted symmetric operator is a projection.
Every replica weight retains the original full-family dimension.

### Real powers with fixed symmetric coordinates — planned existing-lemma use

The Bell power comparison retains one supplied symmetric isometry Z and
forms the product of means of Zᴴ A Z, exactly as in the lower norm estimates.
`replicaMetric_symProj_compressions_posDef_commute` and
`MeanTree.eval_intertwine` give the band equations. Ordered multiplication
then gives the equation for the same product, and `PosSemidef.rpow_intertwine`
applies with rectangular map Zᴴ P. No second compression is selected.

### Norms under projected Hermitian intertwining — existing lemmas (2026-10-11)

The projected norm comparison reuses `Matrix.norm_toLp_mulVec_of_isometry`
for the rectangular isometry and `IsHermitian.conjTranspose_intertwine`
for the reversed equation. The remaining estimate is contractivity of an
orthogonal projection. No positivity or equality of the isometry range
with the projected range is needed.

### Cutoff estimates in fixed symmetric coordinates — existing lemmas (2026-10-12)

The compressed inverse-norm estimate applies the existing exterior cutoff
bound to the projected vector. The same-isometry real-power identity and
`Matrix.norm_projected_le_of_isometric_intertwine` compare the inverse norms.
No inverse-power vector or symmetric coordinates are chosen a second time.
The region map removes the physical insertion region and then embeds into
the original family, so all metric weights retain the full-family dimension.

### Commutation with terminal band products — candidate (2026-10-13)

- **Pattern:** Prove commutation with each factor of the ordered band product,
  use `Commute.list_prod_right` and `List.mem_ofFn`, then identify the old
  and new terminal inputs by their definitions.
- **Seen:** `TransportData.commute_permOp_input` in
  `Representation/ReplicaTransport/States.lean` and
  `TransportData.commute_labelProj_singleton_input` in
  `Representation/ReplicaTransport/LabelPreservation.lean`.
- **Decision:** Two occurrences across two files. The existing list-product
  commutation theorem handles the algebra; no new tactic is introduced.
  A third mathematical consumer would justify a general theorem for
  terminal-input commutation.
- **Scope:** Preserve the supplied terminal labels and increasing band order,
  including an empty product. No positivity or finiteness assumption on
  the history and choice sets is used.

### Regional expectations in product coordinates — candidate (2026-10-13)

- **Pattern:** Split each copy into complementary and regional coordinates,
  identify the regional operator as an identity tensor factor, and apply
  the partial-trace identity for a pure tensor power.
- **Seen:** `norm_sq_one_sub_labelCutoff_subsystemPerm_prod` in
  `Representation/SubsystemLabelCoordinates.lean` and
  `re_inner_exp_labelEntropy_subsystemPerm_prod` in
  `Representation/SubsystemLabelExponential.lean`.
- **Existing results:** `labelProj_subsystemPerm_submatrix` identifies the
  regional projections; `partialTraceLeft_vecMulVec_prod` and
  `trace_partialTraceLeft_mul` give the corresponding trace pairing.
- **Decision:** Two occurrences across two files. The projection-norm and
  exponential-expectation proofs already reuse these results; no new
  tactic is introduced. A third use would justify a common expectation
  identity for an arbitrary regional operator.
- **Scope:** The one-copy vector need not be normalized. Preserve the actual
  regional marginal, the complementary-first coordinate order, zero
  replicas, and empty local coordinate sets.

### Tensor order from positive factors — promoted helper (2026-10-13)

- **Pattern:** Compare two tensor products by changing one factor at a time.
  Each comparison is the monotonicity of a positive linear map obtained by
  tensoring with a fixed positive semidefinite matrix.
- **Occurrences:** The two factor comparisons in `Matrix.finKronecker_mono`
  and the two formerly explicit comparisons in `Entropy.RestoringNorm`.
- **Helper:** `Matrix.kronecker_mono_of_posSemidef` in
  `Algebra/FiniteKroneckerOrder.lean` assumes `A ≤ B`, `C ≤ D`, positivity
  of `B` and positivity of `C`, and proves `A ⊗ C ≤ B ⊗ D`.
- **Reuse:** The finite induction and the scalar-identity bound in
  `Entropy/RestoringNorm.lean` both apply this helper. The latter retains
  its possibly indefinite lower first factor; no assumption was added.
- **Implementation:** `PositiveLinearMap.mk₀`, `kroneckerBilinear`, and
  `PosSemidef.kronecker` suffice. Use `Matrix.nonneg_iff_posSemidef.mp`
  explicitly inside the constructor when elaboration unfolds matrix order.
  No new tactic is needed.

### Selected-marginal exponential comparisons — existing lemmas (2026-10-13)

The comparison after spectral selection reuses `Matrix.finKronecker_mono`
for the actual marginal order and
`Matrix.PosSemidef.re_trace_mul_le_re_trace_mul` for the positive exponential
trace pairing. `IsSelfAdjoint.exp_nonneg` supplies positivity for every real
exponential parameter. No commutation assumption or new tactic is needed.
The scalar factor in a finite tensor power is obtained entrywise from
`Finset.prod_mul_distrib`; this proof is recorded as a single occurrence,
with no new abstraction. The zero-copy product and the original selected
mass are preserved.

### Three signed selected moments — existing lemmas (2026-10-14)

The sharp leaf argument reuses
`Matrix.PosSemidef.re_trace_mul_exp_sum_le_prod` for three commuting
observables. One region-parameterized local estimate combines spectral
selection and the existing iid signed moments for U, U union Y, and Y.
The positive and negative rates retain their separate coefficients;
three cube roots contribute one inverse selection-mass power. The Bell
expectation identity transports the same central label function through
the actual isometry. No new tactic or duplicated iid proof is introduced,
and every replica metric retains the original full-family weights.

### Supplied-sector logarithmic conditioning — existing lemmas (2026-10-14)

The upper tree comparison reuses `MeanTree.commute_eval_right`, vector
mean Jensen, support-aware log Jensen, and the existing inverse-power
normalization theorem. A single quadratic contraction lemma is evaluated
at the commuting root, so the exact supplied mass is extracted once,
before the terminal-weighted product is expanded. The Euclidean pairing
conversion uses directed rewrites rather than commutative simplification.
No new tactic or duplicate tree induction is introduced.

### Same-sector conditioning across ordered bands — candidate (2026-10-14)

- **Pattern:** Split the logarithm of a commuting ordered product, apply one
  fixed projection/vector bound in every summand, and undo normalization once.
- **Reuse:** `cfc_log_listProd_ofFn`, the supplied-projection single-band upper
  theorem, and inverse-power logarithmic Jensen already supply the substantive
  steps. The multi-band theorem keeps the exact shared mass power rather than
  recreating normalization separately in each consumer.
- **Consumer:** The selected Bell postvector theorem derives actual metric and
  auxiliary-label commutations before applying that analytic theorem. A private
  weighted-affine-sum identity accounts for terminal weights summing to one.
- **Decision:** Two mathematical interfaces and one local scalar helper suffice;
  no new tactic, simp set, instance budget or proof option is introduced. The
  finite-Pi coordinate decision procedures match the accepted sharp-leaf module.

### Literal selected-sector mass and pin transport — existing lemmas (2026-10-14)

- **Pattern:** Specialize a real central-label observable to the indicator of
  one supplied irreducible label, then use the actual insertion isometry to
  preserve its projected norm. This retains the label rather than selecting
  another sector after changing coordinates.
- **Reuse:** `norm_toLp_mulVec_of_isometry` gives norm preservation, and
  `norm_projected_le_of_isometric_intertwine` handles the adjoint orientation
  and orthogonal-projection contraction for real powers. No new inner-product
  calculation, functional-calculus proof or projection tactic is needed.
- **State equality:** The supplied site Bell identity is pulled back through
  the explicit witness bijection. Pure-tensor symmetry and auxiliary-label
  commutation upgrade the range pin to the inserted symmetric pin, with the
  scalar coefficient unchanged. The exact squared coefficient is established
  by the existing complex norm and real square-root identities.
- **Decision:** Reuse the named finite-Pi decision procedures of the literal
  postvector definition. One local coordinate-action equality is sufficient;
  there is no new tactic, simp set, instance budget or proof option.

### Sharp supplied-sequence logarithmic rate

- The selected-sector mass identity and actual inverse transport are applied to
  one supplied physical label sequence; no new transport or norm tactic is used.
- The scalar logarithm calculation reuses the accepted Bell remainder and its
  fixed-parameter limit. The sharp mass exponent requires a separate compact-
  interval error bound, so this is not a fourth copy of a common tactic pattern.
- Enumeration reuses the accepted compressed metric/prevector equalities and
  equivariant symmetric-projection theorem. This is the second actual rate
  consumer after the rough upper bound; no new coordinate tactic is introduced.

### Weighted monomial recovery at common evaluation points — shared theorem (2026-10-28)

- **Consumers:** The two-marker theorem in `Algebra/WeightedFrequencySchmidtRank.lean`
  and the one-marker theorem in `Algebra/OneMarkerWeightedSchmidtRank.lean`.
- **Pattern:** Apply monomial recovery to one injectively indexed finite support,
  contract the arbitrary scalar weights at the same evaluation points, then use
  the finite-sum operator-Schmidt-rank bound. Zero and dependent coefficients
  require no separate argument.
- **Decision:** Move the existing weighted argument to
  `Matrix.operatorSchmidtRank_sum_smul_le_of_injective_monomial_evaluations`
  in `Algebra/MonomialEvaluationSchmidtRank.lean`; both consumers reuse it.
  No new tactic or duplicate interpolation calculation is introduced.

### Weighted pure-state projection identities — shared lemma (2026-10-23)

- **Seen:** The equal-weight pure-state trace distance and the optimized
  pure-state trace-norm error use the same rank-one projection identities.
- **Decision:** `Matrix.re_trace_abs_vecMulVec_sub_smul_eq` in
  `Analysis.WeightedPureStateTraceNorm` contains the projection calculation
  once. The old trace-distance theorem specializes its coefficient to one;
  `Analysis.OptimizedPureStateTraceError` uses it after positive rescaling.
- **Mechanism:** Existing `module` handles scalar polynomial identities
  after distributivity; existing functional-calculus square-root uniqueness
  identifies the absolute value. No new tactic is needed.
- **Caveat:** The density coefficient is nonnegative in the weighted
  identity. The final minimum separately treats all complex coefficients
  by Hermitian-part contraction and trace duality.

### Uniform-weight Jensen bounds for entropy contributions (2026-10-23)

- **Seen:** `Analysis.ProbabilityEntropy` and
  `Analysis.ProbabilityEntropyConcentration` apply concavity of `negMulLog`
  with reciprocal-cardinality weights, then multiply by the cardinality.
- **Candidate:** `Entropy.sum_negMulLog_le_mass_log_card` now gives the
  finite-mass estimate, including an empty set. A future consolidation can
  put this lower-level estimate before the normalized support theorem and
  derive the latter from it. There are two occurrences, below the promotion
  threshold; no new tactic or simp set is introduced.

## Candidate: ordered eigenvalue tails as finite probability tails (2026-10-23)

The conversion from a natural-number interval of descending eigenvalues to the
complement of a filtered finite ordinal appears in
`Analysis.VonNeumannEntropySpectralTail` and `Entropy.RenyiRankLowerBound`
(the latter is developed separately). Both use `Fin.sum_univ_eq_sum_range`
and the equality between a filtered range and an interval. A third independent
use should promote this conversion to a shared eigenvalue-sum lemma.

### Identity contractions in trace products — existing lemma (2026-10-23)

- **Seen:** The imaginary-weight estimate and the empty product in
  `Analysis.TraceHolderMulti` need the identity operator norm bound.
- **Decision:** Reuse `Matrix.l2_opNorm_one_le` from
  `Analysis.ContractionChain`, rather than repeating its private proof.
- **Caveat:** The bound is at most one and includes an empty coordinate
  space. Neither use introduces a nonempty-space assumption.
- **Mechanism:** A direct mathematical lemma suffices; no tactic is added.

### Degree-one coefficient recurrence — candidate (2026-10-22)

- **Seen:** The private coefficient recurrences in `Algebra/OrderedPolynomialGaps.lean`
  and `Algebra/CommutingPolynomialGaps.lean`.
- **Pattern:** Left multiplication by `C D + C T * X` gives the same two-term
  coefficient recurrence, with constant and leading-coefficient boundaries.
- **Decision:** Reuse the polynomial coefficient lemmas. There are two consumers;
  a third use would justify one shared recurrence lemma.

### Isolated ground projection as an indicator — candidate (2026-10-22)

- **Pattern:** On a finite Hermitian spectrum contained in one isolated energy
  and a higher interval, express the complement of the closed threshold
  projection as the indicator of the isolated energy.
- **Seen:** `Analysis/PowerSpectralFilter.lean`, local `hPg`; the corresponding
  local `hPg` in `Analysis/ChebyshevSpectralFilter.lean` (proposed in QICLean
  PR 860).
- **Decision:** Two occurrences across the two spectral-filter developments.
  Retain the short local calculations for now; consider a shared projection
  lemma if a third consumer requires the same identification.

### Finite-sum upper bounds for positive contractions — existing lemmas (2026-10-22)

- **Pattern:** Sum the bounds $h_i\le1$ and identify the constant sum with
  the number of terms times the identity.
- **Seen:** The spectral calculation in `Analysis/PhysicalPowerFilter.lean`
  and both the exponential estimate and logarithmic threshold in
  `Analysis/PhysicalPowerFilterLowerGap.lean`.
- **Reuse:** `Finset.sum_le_sum`, `Finset.sum_const`, and
  `Nat.cast_smul_eq_nsmul` already supply the general inequality and its
  scalar normalization. These existing lemmas suffice; no new tactic or
  additional finite-sum theorem is introduced. The new evaluation of an
  operator upper bound on a unit eigenvector is shared by the two new
  estimates as one private mathematical lemma.

### Equality decisions in finite coordinates — existing lemma (2026-10-23)

- **Occurrences:** The one-dimensional and two-qubit applications in
  `QICLeanTest/AGSPFavorableEntropyAxioms.lean`, and both configuration factors
  in `QICLean/Entropy/AGSPRegionalEntropy.lean`.
- **Reuse:** `Subsingleton.elim` identifies a classically chosen `DecidableEq`
  value with the available value before applying a theorem whose matrix
  expressions contain those decisions.
- **Decision:** Rewrite only the decision values. The operators, vectors,
  regions, ranks and shrinking hypotheses are unchanged. The existing lemma
  suffices; no new theorem, tactic or simp set is required.

### Two nonnegative weights bounded by their sum — candidate (2026-10-26)

- **Seen:** The local `hpair` arguments in `Analysis/DominantEigenvector.lean`
  and `Analysis/DominantEigenvectorUniqueness.lean`.
- **Pattern:** For distinct indices, identify the sum of two nonnegative
  weights with the sum over their pair, then bound it by the total sum.
- **Reuse:** `Finset.sum_pair` and
  `Finset.sum_le_sum_of_subset_of_nonneg` give the two steps directly.
  There are two occurrences across two files. Retain these existing lemmas;
  a third occurrence would justify considering a combined inequality.

### Finite matrix-unit sums — candidate (2026-10-29)

- **Seen:** The normalization and channel formula in `Kraus/Stochastic.lean`
  reindex a finite pair alphabet by `finProdFinEquiv.sum_comp`, then combine
  scalar coefficients with `Matrix.singleAddMonoidHom.map_sum`.
- **Reuse:** Keep the existing equivalence and additive homomorphism lemmas.
  These are two occurrences in one file; no new tactic is warranted.

### Extending density-state convergence to all matrix inputs — existing decomposition (2026-10-29)

- **Seen:** The primitivity proof in `Channel/WolfTheorem67.lean` extends
  convergence from density matrices to all matrices; the bounded-orbit proof
  in `Channel/FixedPoint/MeanErgodicProjection.lean` uses the same positive-part
  reduction for boundedness.
- **Reuse:** Total trace normalization handles zero-trace inputs. Apply the
  existing four-positive-semidefinite-parts decomposition to the identity
  map, then combine convergence by subtraction and scalar multiplication.
  `ContinuousLinearMap.tendsto_of_tendsto_apply_of_finiteDimensional` supplies
  convergence in operator norm.
- **Decision:** No new tactic. The convergence helper stays private until
  another production consumer needs the same limit statement.

### Peripheral phases and finite cyclicity — existing structures (2026-10-29)

- **Seen:** `Peripheral/AbstractEigenvectors.lean` and
  `Peripheral/IrreducibleSchwarz.lean` use the same unit-modulus cancellation
  in the weighted Schwarz equality, peripheral products, and normalization.
- **Reuse:** `Complex.conj_mul'` handles conjugate-phase cancellation;
  `SchwarzMap.mem_rightMultiplicativeDomain_iff` and its full-domain version
  handle product preservation. No separate phase tactic is introduced.
- **Shared mathematics:** `peripheralEigenvalues_eq_range_exp_of_mul_mem`
  factors the finite-set cyclicity argument out of `CyclicGroupKraus`.
  `Module.End.eigenvectors_linearIndependent'` and
  `LinearIndependent.fintype_card_le_finrank` give the order bound.
- **Compatibility:** finite-Kraus peripheral-unitary declarations now call
  the abstract results. Their historical adjoint-weight arguments are retained
  and explicitly acknowledged in the proof to preserve named-argument callers.

### Spectral support and complementary cuts — shared lemmas (2026-10-29)

- `Matrix.IsHermitian.supportProj_eq_cfc` expresses the range projection
  through functional calculus; its transpose identity now reuses this lemma.
- `Matrix.operatorSchmidtRank_reindex_prodComm` and
  `Entropy.operatorSchmidtRank_cutOperator_compl_eq` express invariance under
  exchange of tensor factors and complementary regions. The two-sided support
  estimate combines the existing one-sided bounds through these identities.
- No additional tactic or parallel definition of a support projection is used.

### The two-factor projector-gap defect — promoted (2026-10-29)

- **Pattern:** Expand the projector-gap defect of a tensor sum as the sum of
  the two factor defects and the tensor product of the two orthogonal
  complements.
- **Defined in:** `Analysis/DoubledSystemGap.lean`, `Matrix.tensorSum_gap_eq`
  and `Matrix.PosSemidef.tensorSum_gap`.
- **Refactored occurrences:** The original doubled-Hamiltonian identity and
  gap theorem are now direct specializations. The product-ancilla application
  uses the same identity with different factor dimensions and energies.
- **Notes:** `Matrix.PosSemidef.gap_mono` handles the capped lower bound;
  neither it nor the tensor-sum result assumes an attained excited energy.

### Elementary operator Schmidt products — promoted (2026-10-29)

- **Pattern:** An elementary Kronecker product has a one-term decomposition;
  the identity is its specialization.
- **Abstraction:** The existing private proof in
  `OneMarkerWeightedSchmidtRank.lean` is relocated unchanged to the small
  `OperatorSchmidtProducts.lean` leaf as
  `Matrix.operatorSchmidtRank_kronecker_le_one`, with
  `Matrix.operatorSchmidtRank_one_le` as the identity specialization.
- **Refactoring:** The one-marker consumer imports this leaf and the private
  duplicate is removed. `OperatorSchmidtBounds.lean` remains unchanged.
  The second factor needs `Finite`, rather than a supplied `Fintype`.

## Candidate: quadratic bounds on ordered spectral spans (2026-10-29)

- **Seen:** The two matrix comparisons in `Analysis/WeylMonotonicity.lean`
  bound quadratic forms on the first or last eigenvectors using support of
  the coordinate representation, antitonicity, and Parseval's identity.
- **Reused:** Both comparisons use the existing private finite-dimensional
  intersection theorem and quadratic spectral expansion.
- **Decision:** Two occurrences in one file do not meet the rule of three;
  retain the bounded proofs and consider a span-bound lemma at a third
  mathematical consumer.

### Actual relative spectral cutoffs — existing perturbation lemma (2026-10-29)

- **Consumer:** `Analysis/RelativeLowEnergyCloseness.lean` applies the existing
  finite-window perturbation estimate in both directions to actual canonical
  low-energy spaces. The original and perturbed minima are derived from their
  last ordered eigenvalues and the actual restricted residual.
- **Reuse:** A single private numerical helper proves both window budgets;
  `ContinuousLinearMap.le_opNorm` on the actual spectral subtype derives the
  vector residual. The reverse cutoff inclusion is ordinary span monotonicity.
- **Decision:** No new low-energy predicate, supplied basis, projection map,
  or ground-energy comparison is introduced. No new tactic is needed.

### Capped geometric entropy tails — existing helpers (2026-10-29)

- **Seen:** `Channel.AGSPGeometricTails` and `Channel.AGSPGeneralTails` iterate
  the same homogeneous orthogonal contraction and compare the resulting
  orthogonal remainder with a Ky Fan tail.
- **Reuse:** Expose the existing
  `LinearMap.inner_pow_eq_zero_and_norm_sq_le` and
  `Matrix.one_sub_kyFanNorm_le_of_orthogonal_decomposition` with their proofs
  unchanged. The favorable and general entropy estimates use the same finite
  `Entropy.probabilityEntropy_le_of_rankTailBounds` summation.
- **Scope:** The general estimate retains the actual initial overlap and
  shrinking factor; no new approximate-projector predicate or supplied tail
  replaces the actual operator argument.
