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
