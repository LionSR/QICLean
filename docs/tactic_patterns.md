# Tactic pattern ledger

Record repeated proof patterns before introducing a new tactic. Prefer an
existing theorem, then a reusable lemma or simp set; promote a new abstraction
only after at least three genuine occurrences across two files. Occurrences
in a regression file are not additional mathematical consumers.

## Promoted

No new tactic or automation is introduced for shifted spectral truncation.
The proofs reuse existing functional-calculus identities, projection
rank/trace comparison, range-of-composition, and scalar real-power bounds.

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

### Rectangular real-power transport — promoted lemma (2026-10-08)

- **Pattern:** Express a real matrix power as a finite Hermitian functional
  calculus and transport it along a rectangular intertwiner.
- **Seen:** Once in `GeometricMeanDerivativeIntertwine.lean` and twice in
  `GeometricMeanIntertwine.lean`, for the input and whitened matrices.
- **Abstraction:** `Matrix.PosSemidef.rpow_intertwine` in
  `RealPowerIntertwine.lean`; all three occurrences use this lemma.
- **Caveats:** Every real exponent is allowed. Negative powers vanish on the
  kernel, and exponent zero gives the identity. No isometry is required.

### Rectangular sandwich intertwining — promoted lemmas (2026-10-08)

- **Pattern:** Move a Hermitian factor through a rectangular intertwiner,
  and its adjoint through the conjugate transpose, to transport a sandwich.
- **Seen:** Resolvents in `PowerDerivativeIntertwine.lean`, real powers in
  `GeometricMeanDerivativeIntertwine.lean`, and the leaf and root normalization
  factors in `MeanTreeDerivativeIntertwine.lean`.
- **Abstraction:** `Matrix.IsHermitian.conjTranspose_intertwine` and
  `Matrix.IsHermitian.sandwich_intertwine`, in
  `Algebra/MatrixSandwichIntertwine.lean`. All three consumers reuse these
  identities; compression uses the adjoint identity with the families exchanged.
- **Caveats:** Directions are arbitrary. Rectangular products require matrix
  associativity. Neither isometry nor nonempty index sets are assumed.

## Candidates

### Finite-spectrum functional-calculus scalar reduction — candidate (2026-10-07)

- **Pattern:** Rewrite matrices as Hermitian functional calculi, combine
  products with `← hA.cfc_mul`, and reduce the equality to a pointwise
  threshold split followed by scalar simplification.
- **Seen:** In `QICLean/Analysis/ShiftedDensityTruncation.lean`,
  `IsHermitian.isStarProjection_spectralProjectionGE`,
  `PosSemidef.commute_add_smul_one_rpow_spectralProjectionGE`,
  `PosSemidef.shiftedPowerHead_eq_cfc`, and
  `PosSemidef.shiftedPowerHead_mul_shiftedPowerTail` are representative
  occurrences. Their scalar conclusions differ.
- **Abstraction:** Continue using the existing `Matrix.IsHermitian.cfc_mul`
  and `cfc_congr` results. A specialized automation rule is not justified
  by repetition in this single module.
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
