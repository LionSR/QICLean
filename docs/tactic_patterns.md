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
